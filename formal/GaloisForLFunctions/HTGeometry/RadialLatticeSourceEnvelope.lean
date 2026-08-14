import GaloisForLFunctions.HTGeometry.ZeroMeanBVLatticeEnvelope
import GaloisForLFunctions.HTGeometry.HalfDensityEnvelopePolarCharge

/-!
# The radial lattice source and its half-density envelope

The physical lattice charge of a compactly supported source at radial scale `a` is the sum

```text
Q(a) = ∑_{n ≥ 1} g (n / a),
```

which has finitely many nonzero terms.  Its square-root normalization `Q(a) / √a` is the exact
radial source of the one-sided Poisson--Muntz formula, and the BV quadrature envelope bounds it by
`2 Var(g) / √a`.  Writing `a = λ exp t` turns that into the **half-density envelope**

```text
|b_λ(t)| ≤ (2 Var(g) / √λ) exp (-t/2),
```

so the source's squared mass on the half line is at most `(2 Var(g))² / λ`, unconditionally, and
the polar-charge estimate applies to it with only a primitive bound left to supply.
-/

noncomputable section

open MeasureTheory Set

namespace HTGeometry

/-- The physical lattice charge of a compactly supported source at radial scale `a`. -/
def latticeCharge (g : ℝ → ℂ) (a : ℝ) : ℂ := ∑' i : ℕ, g (((i : ℝ) + 1) / a)

/-- The square-root normalized radial source. -/
def radialLatticeSource (g : ℝ → ℂ) (a : ℝ) : ℂ := latticeCharge g a / (Real.sqrt a : ℂ)

/-- Beyond the support the lattice terms vanish, so the charge is a finite sum. -/
theorem latticeCharge_eq_sum {g : ℝ → ℂ} {L a : ℝ} (ha : 0 < a)
    (hvan : ∀ x : ℝ, L < x → g x = 0) {n : ℕ} (hn : L < ((n : ℝ) + 1) / a) :
    latticeCharge g a = ∑ i ∈ Finset.range n, g (((i : ℝ) + 1) / a) := by
  refine tsum_eq_sum ?_
  intro i hi
  refine hvan _ ?_
  have hin : (n : ℝ) ≤ (i : ℝ) := by
    have : n ≤ i := Nat.le_of_not_lt (by simpa using hi)
    exact_mod_cast this
  calc L < ((n : ℝ) + 1) / a := hn
    _ ≤ ((i : ℝ) + 1) / a := by
        have hnum : ((n : ℝ) + 1) ≤ ((i : ℝ) + 1) := by linarith
        gcongr

/-- The radial source is the square-root lattice quadrature at the floor index. -/
theorem radialLatticeSource_eq_quadrature {g : ℝ → ℂ} {L a : ℝ} (ha : 0 < a)
    (hvan : ∀ x : ℝ, L < x → g x = 0) {n : ℕ} (hn : L < ((n : ℝ) + 1) / a) :
    radialLatticeSource g a = sqrtRadialLatticeQuadrature g a n := by
  have hs : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [radialLatticeSource, latticeCharge_eq_sum ha hvan hn, sqrtRadialLatticeQuadrature,
    positiveLatticeQuadrature, Complex.real_smul, Complex.real_smul]
  have hreal : Real.sqrt a * (1 / a) = (Real.sqrt a)⁻¹ := by
    have hsa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    have hsne : Real.sqrt a ≠ 0 := ne_of_gt hs
    field_simp
    linarith [hsa]
  have hkey : ((Real.sqrt a : ℝ) : ℂ) * (((1 / a : ℝ)) : ℂ) = (((Real.sqrt a : ℝ)) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_inv]
  rw [← mul_assoc, hkey, div_eq_inv_mul]

/-- **The square-root envelope of the radial lattice source.** -/
theorem norm_radialLatticeSource_le {g : ℝ → ℂ} {L a : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hint : IntervalIntegrable g volume 0 L) (hvar : BoundedVariationOn g (Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, g x = 0) (hLz : g L = 0)
    (hvan : ∀ x : ℝ, L < x → g x = 0) :
    ‖radialLatticeSource g a‖ ≤ (2 / Real.sqrt a) * (eVariationOn g (Icc 0 L)).toReal := by
  set n : ℕ := ⌊a * L⌋₊ with hndef
  have haL : (0 : ℝ) ≤ a * L := by positivity
  have hfl : (n : ℝ) ≤ a * L := Nat.floor_le haL
  have hfl' : a * L < (n : ℝ) + 1 := Nat.lt_floor_add_one (a * L)
  have hn1 : (n : ℝ) / a ≤ L := by
    rw [div_le_iff₀ ha]
    linarith [hfl]
  have hn2 : L < ((n : ℝ) + 1) / a := by
    rw [lt_div_iff₀ ha]
    linarith [hfl']
  rw [radialLatticeSource_eq_quadrature ha hvan hn2]
  exact norm_sqrtRadialLatticeQuadrature_le_two_mul_variation_div_sqrt ha hn1 hn2.le
    hint hvar hmean hLz

/-! ### The source in the logarithmic radial variable -/

/-- The radial source read in the logarithmic variable, as a real function. -/
def radialLogSource (g : ℝ → ℂ) (lam : ℝ) (t : ℝ) : ℝ :=
  (radialLatticeSource g (lam * Real.exp t)).re

/-- **The half-density envelope.**  In the logarithmic variable the square-root envelope is the
exact half density. -/
theorem abs_radialLogSource_le {g : ℝ → ℂ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hint : IntervalIntegrable g volume 0 L) (hvar : BoundedVariationOn g (Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, g x = 0) (hLz : g L = 0)
    (hvan : ∀ x : ℝ, L < x → g x = 0) (t : ℝ) :
    |radialLogSource g lam t|
      ≤ (2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam) * Real.exp (-t / 2) := by
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have ha : (0 : ℝ) < lam * Real.exp t := by positivity
  have hbase := norm_radialLatticeSource_le (g := g) (L := L) ha hL hint hvar hmean hLz hvan
  have hre : |radialLogSource g lam t| ≤ ‖radialLatticeSource g (lam * Real.exp t)‖ := by
    rw [radialLogSource]
    exact Complex.abs_re_le_norm _
  refine hre.trans (hbase.trans (le_of_eq ?_))
  have hsq : Real.sqrt (lam * Real.exp t) = Real.sqrt lam * Real.exp (t / 2) := by
    rw [Real.sqrt_mul hlam.le]
    congr 1
    rw [show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hne : Real.exp (t / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hsl : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hEn : Real.exp (-t / 2) = 1 / Real.exp (t / 2) := by
    rw [show (-t / 2 : ℝ) = -(t / 2) by ring, Real.exp_neg]
    ring
  rw [hsq, hEn]
  field_simp

/-! ### Continuity -/

/-- Away from the support the lattice sum is locally a fixed finite sum, so the charge is
continuous in the radial scale. -/
theorem continuousAt_radialLogSource {g : ℝ → ℂ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hgc : Continuous g) (hvan : ∀ x : ℝ, L < x → g x = 0) (t : ℝ) :
    ContinuousAt (radialLogSource g lam) t := by
  set N : ℕ := ⌈lam * Real.exp (t + 1) * L⌉₊ with hNdef
  have hbig : ∀ s : ℝ, s < t + 1 → L < ((N : ℝ) + 1) / (lam * Real.exp s) := by
    intro s hs
    have hexp : (0 : ℝ) < Real.exp s := Real.exp_pos s
    have ha : (0 : ℝ) < lam * Real.exp s := by positivity
    rw [lt_div_iff₀ ha]
    have hmono : Real.exp s ≤ Real.exp (t + 1) := Real.exp_le_exp.mpr hs.le
    have hle : lam * Real.exp s * L ≤ lam * Real.exp (t + 1) * L := by
      have h1 : lam * Real.exp s ≤ lam * Real.exp (t + 1) :=
        mul_le_mul_of_nonneg_left hmono hlam.le
      exact mul_le_mul_of_nonneg_right h1 hL
    have hceil : lam * Real.exp (t + 1) * L ≤ (N : ℝ) := Nat.le_ceil _
    linarith
  have heq : ∀ s : ℝ, s < t + 1 →
      radialLogSource g lam s
        = ((∑ i ∈ Finset.range N, g (((i : ℝ) + 1) / (lam * Real.exp s)))
            / (Real.sqrt (lam * Real.exp s) : ℂ)).re := by
    intro s hs
    have hexp : (0 : ℝ) < Real.exp s := Real.exp_pos s
    have ha : (0 : ℝ) < lam * Real.exp s := by positivity
    rw [radialLogSource, radialLatticeSource, latticeCharge_eq_sum ha hvan (hbig s hs)]
  have hcont : ContinuousAt (fun s : ℝ =>
      ((∑ i ∈ Finset.range N, g (((i : ℝ) + 1) / (lam * Real.exp s)))
        / (Real.sqrt (lam * Real.exp s) : ℂ)).re) t := by
    have hden : Continuous fun s : ℝ => ((Real.sqrt (lam * Real.exp s) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_const.mul Real.continuous_exp))
    have hnum : Continuous fun s : ℝ =>
        ∑ i ∈ Finset.range N, g (((i : ℝ) + 1) / (lam * Real.exp s)) := by
      refine continuous_finsetSum _ fun i _ => hgc.comp ?_
      refine continuous_const.div (continuous_const.mul Real.continuous_exp) fun s => ?_
      have : (0 : ℝ) < lam * Real.exp s := by positivity
      exact ne_of_gt this
    have hne : ((Real.sqrt (lam * Real.exp t) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ?_))
      positivity
    exact (Complex.continuous_re.continuousAt).comp
      ((hnum.continuousAt).div (hden.continuousAt) hne)
  refine hcont.congr ?_
  filter_upwards [eventually_lt_nhds (by linarith : t < t + 1)] with s hs
  exact (heq s hs).symm

theorem continuous_radialLogSource {g : ℝ → ℂ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hgc : Continuous g) (hvan : ∀ x : ℝ, L < x → g x = 0) :
    Continuous (radialLogSource g lam) :=
  continuous_iff_continuousAt.mpr fun t =>
    continuousAt_radialLogSource (L := L) hlam hL hgc hvan t

/-! ### The two consequences -/

/-- **`(4)` for the radial lattice source.**  Its squared mass on the half line is at most the
squared envelope constant — unconditionally. -/
theorem integral_sq_radialLogSource_le {g : ℝ → ℂ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hgc : Continuous g) (hint : IntervalIntegrable g volume 0 L)
    (hvar : BoundedVariationOn g (Icc 0 L)) (hmean : ∫ x in (0 : ℝ)..L, g x = 0)
    (hLz : g L = 0) (hvan : ∀ x : ℝ, L < x → g x = 0) :
    (∫ t in Ioi (0 : ℝ), radialLogSource g lam t ^ 2)
      ≤ (2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ 2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn g (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    positivity
  have hcont := continuous_radialLogSource (L := L) hlam hL hgc hvan
  exact integral_sq_le_of_envelope hcont.measurable hK
    (fun s _ => abs_radialLogSource_le hlam hL hint hvar hmean hLz hvan s)

/-- **`(18)` for the radial lattice source.**  Only the primitive bound is left to supply: every
integrability hypothesis of the abstract polar estimate is discharged by the envelope. -/
theorem abs_polarCharge_radialLogSource_le {g : ℝ → ℂ} {L lam a M : ℝ} (hlam : 0 < lam)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hgc : Continuous g) (hint : IntervalIntegrable g volume 0 L)
    (hvar : BoundedVariationOn g (Icc 0 L)) (hmean : ∫ x in (0 : ℝ)..L, g x = 0)
    (hLz : g L = 0) (hvan : ∀ x : ℝ, L < x → g x = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive (radialLogSource g lam) t| ≤ M) :
    |polarCharge (radialLogSource g lam) a|
      ≤ 4 * M * (2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam)
        + 4 * (2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ 2 * (eVariationOn g (Icc 0 L)).toReal / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn g (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    positivity
  have hcont := continuous_radialLogSource (L := L) hlam hL hgc hvan
  exact abs_polarCharge_le_of_envelope hcont.measurable
    (fun x y => intervalIntegrable_expHalf_mul hcont x y)
    ha hK (fun s _ => abs_radialLogSource_le hlam hL hint hvar hmean hLz hvan s) hA

/-! ### The real source and the Poisson centre -/

theorem sqrt_mul_exp {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    Real.sqrt (lam * Real.exp t) = Real.sqrt lam * Real.exp (t / 2) := by
  rw [Real.sqrt_mul hlam]
  congr 1
  rw [show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf]
  exact Real.sqrt_mul_self (Real.exp_pos _).le

/-- Complexification does not change the total variation. -/
theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => ((f x : ℝ) : ℂ)) s = eVariationOn f s := by
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, Complex.dist_eq]
    calc |z.re - w.re| = |(z - w).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  refine le_antisymm ?_ ?_
  · have h := (Complex.isometry_ofReal.lipschitz.lipschitzOnWith).comp_eVariationOn_le
      (g := f) (s := s) (Set.mapsTo_univ _ _)
    simpa [Function.comp_def] using h
  · have h := (hre.lipschitzOnWith).comp_eVariationOn_le
      (g := fun x : ℝ => ((f x : ℝ) : ℂ)) (s := s) (Set.mapsTo_univ _ _)
    simpa [Function.comp_def] using h

/-- The complexified lattice charge is the complexification of the real one. -/
theorem latticeCharge_ofReal {f : ℝ → ℝ} {L a : ℝ} (ha : 0 < a)
    (hvan : ∀ x : ℝ, L < x → f x = 0) :
    latticeCharge (fun x => ((f x : ℝ) : ℂ)) a
      = (((∑' i : ℕ, f (((i : ℝ) + 1) / a) : ℝ)) : ℂ) := by
  set n : ℕ := ⌊a * L⌋₊ + 1 with hndef
  have hfl' : a * L < (⌊a * L⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (a * L)
  have hn : L < ((n : ℝ) + 1) / a := by
    rw [lt_div_iff₀ ha, hndef]
    push_cast
    linarith [hfl']
  have hvanC : ∀ x : ℝ, L < x → ((f x : ℝ) : ℂ) = 0 := by
    intro x hx
    rw [hvan x hx]
    simp
  have hzero : ∀ i : ℕ, i ∉ Finset.range n → f (((i : ℝ) + 1) / a) = 0 := by
    intro i hi
    refine hvan _ ?_
    have hin : (n : ℝ) ≤ (i : ℝ) := by
      have : n ≤ i := Nat.le_of_not_lt (by simpa using hi)
      exact_mod_cast this
    calc L < ((n : ℝ) + 1) / a := hn
      _ ≤ ((i : ℝ) + 1) / a := by
          have hnum : ((n : ℝ) + 1) ≤ ((i : ℝ) + 1) := by linarith
          gcongr
  rw [latticeCharge_eq_sum ha hvanC hn, tsum_eq_sum hzero]
  push_cast
  rfl

/-- The real radial source in the logarithmic variable. -/
theorem radialLogSource_ofReal {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam)
    (hvan : ∀ x : ℝ, L < x → f x = 0) (t : ℝ) :
    radialLogSource (fun x => ((f x : ℝ) : ℂ)) lam t
      = (∑' i : ℕ, f (((i : ℝ) + 1) / (lam * Real.exp t))) / Real.sqrt (lam * Real.exp t) := by
  have ha : (0 : ℝ) < lam * Real.exp t := by positivity
  rw [radialLogSource, radialLatticeSource, latticeCharge_ofReal ha hvan]
  rw [← Complex.ofReal_div]
  exact Complex.ofReal_re _

/-- **The full radial source**: the Poisson centre plus the physical lattice charge. -/
def radialFullLogSource (f : ℝ → ℝ) (lam : ℝ) (t : ℝ) : ℝ :=
  radialLogSource (fun x => ((f x : ℝ) : ℂ)) lam t
    + f 0 / (2 * Real.sqrt (lam * Real.exp t))

/-- **`(19d)`.**  The full radial source has the exact half-density envelope. -/
theorem abs_radialFullLogSource_le {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hint : IntervalIntegrable f volume 0 L) (hvar : BoundedVariationOn f (Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, f x = 0) (hLz : f L = 0)
    (hvan : ∀ x : ℝ, L < x → f x = 0) (t : ℝ) :
    |radialFullLogSource f lam t|
      ≤ ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam)
        * Real.exp (-t / 2) := by
  have hsl : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hexp : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hintC : IntervalIntegrable (fun x : ℝ => ((f x : ℝ) : ℂ)) volume 0 L :=
    ⟨hint.1.ofReal, hint.2.ofReal⟩
  have hvarC : BoundedVariationOn (fun x : ℝ => ((f x : ℝ) : ℂ)) (Icc 0 L) := by
    rw [BoundedVariationOn, eVariationOn_ofReal]
    exact hvar
  have hmeanC : ∫ x in (0 : ℝ)..L, ((f x : ℝ) : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal, hmean]
    simp
  have hLzC : ((f L : ℝ) : ℂ) = 0 := by rw [hLz]; simp
  have hvanC : ∀ x : ℝ, L < x → ((f x : ℝ) : ℂ) = 0 := by
    intro x hx
    rw [hvan x hx]
    simp
  have hbody := abs_radialLogSource_le (g := fun x : ℝ => ((f x : ℝ) : ℂ)) (L := L)
    hlam hL hintC hvarC hmeanC hLzC hvanC t
  rw [eVariationOn_ofReal] at hbody
  have hcentre : |f 0 / (2 * Real.sqrt (lam * Real.exp t))|
      = (|f 0| / 2 / Real.sqrt lam) * Real.exp (-t / 2) := by
    rw [sqrt_mul_exp hlam.le, abs_div]
    have hden : |2 * (Real.sqrt lam * Real.exp (t / 2))| = 2 * (Real.sqrt lam * Real.exp (t / 2)) :=
      abs_of_pos (by positivity)
    rw [hden]
    have hEn : Real.exp (-t / 2) = 1 / Real.exp (t / 2) := by
      rw [show (-t / 2 : ℝ) = -(t / 2) by ring, Real.exp_neg]
      ring
    rw [hEn]
    field_simp
  calc |radialFullLogSource f lam t|
      ≤ |radialLogSource (fun x : ℝ => ((f x : ℝ) : ℂ)) lam t|
          + |f 0 / (2 * Real.sqrt (lam * Real.exp t))| := abs_add_le _ _
    _ ≤ (2 * (eVariationOn f (Icc 0 L)).toReal / Real.sqrt lam) * Real.exp (-t / 2)
          + (|f 0| / 2 / Real.sqrt lam) * Real.exp (-t / 2) := by
        rw [hcentre]
        exact add_le_add hbody le_rfl
    _ = ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam)
          * Real.exp (-t / 2) := by ring

theorem continuous_radialFullLogSource {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hfc : Continuous f) (hvan : ∀ x : ℝ, L < x → f x = 0) :
    Continuous (radialFullLogSource f lam) := by
  have hgc : Continuous fun x : ℝ => ((f x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hfc
  have hvanC : ∀ x : ℝ, L < x → ((f x : ℝ) : ℂ) = 0 := by
    intro x hx
    rw [hvan x hx]
    simp
  refine (continuous_radialLogSource (L := L) hlam hL hgc hvanC).add ?_
  refine continuous_const.div (continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_const.mul Real.continuous_exp))) fun t => ?_
  have h : (0 : ℝ) < 2 * Real.sqrt (lam * Real.exp t) := by
    have : (0 : ℝ) < lam * Real.exp t := by positivity
    have := Real.sqrt_pos.mpr this
    positivity
  exact ne_of_gt h

/-- **`(4)` for the full radial source.** -/
theorem integral_sq_radialFullLogSource_le {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hfc : Continuous f) (hint : IntervalIntegrable f volume 0 L)
    (hvar : BoundedVariationOn f (Icc 0 L)) (hmean : ∫ x in (0 : ℝ)..L, f x = 0)
    (hLz : f L = 0) (hvan : ∀ x : ℝ, L < x → f x = 0) :
    (∫ t in Ioi (0 : ℝ), radialFullLogSource f lam t ^ 2)
      ≤ ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ (2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn f (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have h3 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
    positivity
  have hcont := continuous_radialFullLogSource (L := L) hlam hL hfc hvan
  exact integral_sq_le_of_envelope hcont.measurable hK
    (fun s _ => abs_radialFullLogSource_le hlam hL hint hvar hmean hLz hvan s)

/-- **`(18)` for the full radial source.**  Only the primitive bound is left to supply. -/
theorem abs_polarCharge_radialFullLogSource_le {f : ℝ → ℝ} {L lam a M : ℝ} (hlam : 0 < lam)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfc : Continuous f) (hint : IntervalIntegrable f volume 0 L)
    (hvar : BoundedVariationOn f (Icc 0 L)) (hmean : ∫ x in (0 : ℝ)..L, f x = 0)
    (hLz : f L = 0) (hvan : ∀ x : ℝ, L < x → f x = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive (radialFullLogSource f lam) t| ≤ M) :
    |polarCharge (radialFullLogSource f lam) a|
      ≤ 4 * M * ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam)
        + 4 * ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ (2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn f (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have h3 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
    positivity
  have hcont := continuous_radialFullLogSource (L := L) hlam hL hfc hvan
  exact abs_polarCharge_le_of_envelope hcont.measurable
    (fun x y => intervalIntegrable_expHalf_mul hcont x y)
    ha hK (fun s _ => abs_radialFullLogSource_le hlam hL hint hvar hmean hLz hvan s) hA

/-! ### Measurable sources -/

/-- A measurable function bounded below the right endpoint is interval integrable. -/
theorem intervalIntegrable_of_measurable_of_bound_le {f : ℝ → ℝ} (hm : Measurable f) {x y C : ℝ}
    (hb : ∀ t : ℝ, t ≤ max x y → |f t| ≤ C) : IntervalIntegrable f volume x y := by
  have hstep : ∀ u v : ℝ, v ≤ max x y → IntegrableOn f (Ioc u v) := by
    intro u v hv
    refine Integrable.mono' (integrableOn_const (C := C) measure_Ioc_lt_top.ne enorm_ne_top)
      hm.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    simpa [Real.norm_eq_abs] using hb t (le_trans ht.2 hv)
  exact ⟨hstep x y (le_max_right x y), hstep y x (le_max_left x y)⟩

/-- The lattice charge counts at most `a L` nonzero terms, so the radial source is bounded on
every left ray. -/
theorem abs_radialLogSource_le_of_bound {g : ℝ → ℂ} {L lam Cg : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hgb : ∀ x : ℝ, ‖g x‖ ≤ Cg) (hvan : ∀ x : ℝ, L < x → g x = 0) {T t : ℝ} (ht : t ≤ T) :
    |radialLogSource g lam t| ≤ Real.sqrt (lam * Real.exp T) * L * Cg := by
  have hCg : (0 : ℝ) ≤ Cg := le_trans (norm_nonneg _) (hgb 0)
  have ha : (0 : ℝ) < lam * Real.exp t := by positivity
  set a : ℝ := lam * Real.exp t with hadef
  set n : ℕ := ⌊a * L⌋₊ with hndef
  have hfl' : a * L < (n : ℝ) + 1 := Nat.lt_floor_add_one (a * L)
  have hn : L < ((n : ℝ) + 1) / a := by
    rw [lt_div_iff₀ ha]
    linarith [hfl']
  have hcount : (n : ℝ) ≤ a * L := Nat.floor_le (by positivity)
  have hsum : ‖latticeCharge g a‖ ≤ (n : ℝ) * Cg := by
    rw [latticeCharge_eq_sum ha hvan hn]
    calc ‖∑ i ∈ Finset.range n, g (((i : ℝ) + 1) / a)‖
        ≤ ∑ i ∈ Finset.range n, ‖g (((i : ℝ) + 1) / a)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, Cg := Finset.sum_le_sum fun i _ => hgb _
      _ = (n : ℝ) * Cg := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsasq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hre : |radialLogSource g lam t| ≤ ‖latticeCharge g a‖ / Real.sqrt a := by
    rw [radialLogSource, radialLatticeSource]
    refine le_trans (Complex.abs_re_le_norm _) (le_of_eq ?_)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsa]
  have hstep : ‖latticeCharge g a‖ / Real.sqrt a ≤ Real.sqrt a * L * Cg := by
    rw [div_le_iff₀ hsa]
    calc ‖latticeCharge g a‖ ≤ (n : ℝ) * Cg := hsum
      _ ≤ (a * L) * Cg := by nlinarith [hCg, hcount]
      _ = Real.sqrt a * L * Cg * Real.sqrt a := by
          rw [show Real.sqrt a * L * Cg * Real.sqrt a
            = (Real.sqrt a * Real.sqrt a) * L * Cg by ring, hsasq]
  have hmono : Real.sqrt a ≤ Real.sqrt (lam * Real.exp T) := by
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) hlam.le
  calc |radialLogSource g lam t| ≤ ‖latticeCharge g a‖ / Real.sqrt a := hre
    _ ≤ Real.sqrt a * L * Cg := hstep
    _ ≤ Real.sqrt (lam * Real.exp T) * L * Cg := by
        have : (0 : ℝ) ≤ L * Cg := by positivity
        nlinarith [hmono, hsa.le]

/-- The radial source of a measurable compact source is measurable. -/
theorem measurable_radialLogSource {g : ℝ → ℂ} {L lam : ℝ} (hlam : 0 < lam)
    (hgm : Measurable g) (hvan : ∀ x : ℝ, L < x → g x = 0) :
    Measurable (radialLogSource g lam) := by
  have hmeasN : ∀ N : ℕ, Measurable fun t : ℝ =>
      ((∑ i ∈ Finset.range N, g (((i : ℝ) + 1) / (lam * Real.exp t)))
        / (Real.sqrt (lam * Real.exp t) : ℂ)).re := by
    intro N
    have hden : Measurable fun t : ℝ => ((Real.sqrt (lam * Real.exp t) : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_const.mul Real.continuous_exp))).measurable
    have hnum : Measurable fun t : ℝ =>
        ∑ i ∈ Finset.range N, g (((i : ℝ) + 1) / (lam * Real.exp t)) := by
      refine Finset.measurable_sum _ fun i _ => hgm.comp ?_
      exact measurable_const.div ((continuous_const.mul Real.continuous_exp).measurable)
    exact Complex.measurable_re.comp (hnum.div hden)
  refine measurable_of_tendsto_metrizable' Filter.atTop hmeasN (tendsto_pi_nhds.mpr fun t => ?_)
  have ha : (0 : ℝ) < lam * Real.exp t := by positivity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (⌊(lam * Real.exp t) * L⌋₊ + 1)] with N hN
  have hfl' : (lam * Real.exp t) * L < (⌊(lam * Real.exp t) * L⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hNle : ((⌊(lam * Real.exp t) * L⌋₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hn : L < ((N : ℝ) + 1) / (lam * Real.exp t) := by
    rw [lt_div_iff₀ ha]
    linarith [hfl', hNle]
  rw [radialLogSource, radialLatticeSource, latticeCharge_eq_sum ha hvan hn]

/-- The growing branch of a bounded measurable radial source is interval integrable. -/
theorem intervalIntegrable_expHalf_mul_radialLogSource {g : ℝ → ℂ} {L lam Cg : ℝ}
    (hlam : 0 < lam) (hL : 0 ≤ L) (hgm : Measurable g) (hgb : ∀ x : ℝ, ‖g x‖ ≤ Cg)
    (hvan : ∀ x : ℝ, L < x → g x = 0) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * radialLogSource g lam t) volume x y := by
  have hm : Measurable fun t : ℝ => Real.exp (t / 2) * radialLogSource g lam t :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).measurable.mul
      (measurable_radialLogSource hlam hgm hvan)
  refine intervalIntegrable_of_measurable_of_bound_le hm
    (C := Real.exp (max x y / 2) * (Real.sqrt (lam * Real.exp (max x y)) * L * Cg)) ?_
  intro t ht
  have hb := abs_radialLogSource_le_of_bound (T := max x y) hlam hL hgb hvan ht
  have hnn : (0 : ℝ) ≤ Real.sqrt (lam * Real.exp (max x y)) * L * Cg := by
    have hCg : (0 : ℝ) ≤ Cg := le_trans (norm_nonneg _) (hgb 0)
    have : (0 : ℝ) ≤ Real.sqrt (lam * Real.exp (max x y)) := Real.sqrt_nonneg _
    positivity
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (t / 2) ≤ Real.exp (max x y / 2) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  exact mul_le_mul hexp hb (abs_nonneg _) (Real.exp_pos _).le

/-! ### The measurable full source -/

theorem measurable_radialFullLogSource {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam)
    (hfm : Measurable f) (hvan : ∀ x : ℝ, L < x → f x = 0) :
    Measurable (radialFullLogSource f lam) := by
  have hvanC : ∀ x : ℝ, L < x → ((f x : ℝ) : ℂ) = 0 := by
    intro x hx
    rw [hvan x hx]
    simp
  refine (measurable_radialLogSource (L := L) hlam
    (Complex.measurable_ofReal.comp hfm) hvanC).add ?_
  refine measurable_const.div ?_
  exact (continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_const.mul Real.continuous_exp))).measurable

/-- The centre term contributes a constant to the growing branch. -/
theorem expHalf_mul_centre {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    Real.exp (t / 2) * (f 0 / (2 * Real.sqrt (lam * Real.exp t))) = f 0 / (2 * Real.sqrt lam) := by
  have hsl : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hne : Real.exp (t / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [sqrt_mul_exp hlam.le]
  field_simp

theorem intervalIntegrable_expHalf_mul_radialFullLogSource {f : ℝ → ℝ} {L lam Cg : ℝ}
    (hlam : 0 < lam) (hL : 0 ≤ L) (hfm : Measurable f) (hfb : ∀ x : ℝ, |f x| ≤ Cg)
    (hvan : ∀ x : ℝ, L < x → f x = 0) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * radialFullLogSource f lam t)
      volume x y := by
  have hvanC : ∀ z : ℝ, L < z → ((f z : ℝ) : ℂ) = 0 := by
    intro z hz
    rw [hvan z hz]
    simp
  have hgb : ∀ z : ℝ, ‖((f z : ℝ) : ℂ)‖ ≤ Cg := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hfb z
  have h1 := intervalIntegrable_expHalf_mul_radialLogSource (g := fun z : ℝ => ((f z : ℝ) : ℂ))
    (L := L) (Cg := Cg) hlam hL (Complex.measurable_ofReal.comp hfm) hgb hvanC x y
  have h2 : IntervalIntegrable (fun _ : ℝ => f 0 / (2 * Real.sqrt lam)) volume x y :=
    intervalIntegrable_const
  refine (h1.add h2).congr fun t _ => ?_
  show Real.exp (t / 2) * radialLogSource (fun z : ℝ => ((f z : ℝ) : ℂ)) lam t
      + f 0 / (2 * Real.sqrt lam)
    = Real.exp (t / 2) * radialFullLogSource f lam t
  rw [radialFullLogSource, mul_add, expHalf_mul_centre hlam t]

/-- **`(4)` for a measurable full source.** -/
theorem integral_sq_radialFullLogSource_le_of_measurable {f : ℝ → ℝ} {L lam : ℝ} (hlam : 0 < lam)
    (hL : 0 ≤ L) (hfm : Measurable f) (hint : IntervalIntegrable f volume 0 L)
    (hvar : BoundedVariationOn f (Icc 0 L)) (hmean : ∫ x in (0 : ℝ)..L, f x = 0)
    (hLz : f L = 0) (hvan : ∀ x : ℝ, L < x → f x = 0) :
    (∫ t in Ioi (0 : ℝ), radialFullLogSource f lam t ^ 2)
      ≤ ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ (2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn f (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have h3 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
    positivity
  exact integral_sq_le_of_envelope (measurable_radialFullLogSource (L := L) hlam hfm hvan) hK
    (fun s _ => abs_radialFullLogSource_le hlam hL hint hvar hmean hLz hvan s)

/-- **`(18)` for a measurable full source.**  Only the primitive bound is left to supply. -/
theorem abs_polarCharge_radialFullLogSource_le_of_measurable {f : ℝ → ℝ} {L lam a M Cg : ℝ}
    (hlam : 0 < lam) (hL : 0 ≤ L) (ha : 0 ≤ a) (hfm : Measurable f) (hfb : ∀ x : ℝ, |f x| ≤ Cg)
    (hint : IntervalIntegrable f volume 0 L) (hvar : BoundedVariationOn f (Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, f x = 0) (hLz : f L = 0)
    (hvan : ∀ x : ℝ, L < x → f x = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive (radialFullLogSource f lam) t| ≤ M) :
    |polarCharge (radialFullLogSource f lam) a|
      ≤ 4 * M * ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam)
        + 4 * ((2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam) ^ 2 := by
  have hK : (0 : ℝ) ≤ (2 * (eVariationOn f (Icc 0 L)).toReal + |f 0| / 2) / Real.sqrt lam := by
    have h1 : (0 : ℝ) ≤ (eVariationOn f (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have h3 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
    positivity
  exact abs_polarCharge_le_of_envelope (measurable_radialFullLogSource (L := L) hlam hfm hvan)
    (intervalIntegrable_expHalf_mul_radialFullLogSource (L := L) (Cg := Cg) hlam hL hfm hfb hvan)
    ha hK (fun s _ => abs_radialFullLogSource_le hlam hL hint hvar hmean hLz hvan s) hA

end HTGeometry
