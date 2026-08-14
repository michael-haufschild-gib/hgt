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
  exact integral_sq_le_of_envelope (continuous_radialLogSource (L := L) hlam hL hgc hvan) hK
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
  exact abs_polarCharge_le_of_envelope (continuous_radialLogSource (L := L) hlam hL hgc hvan)
    ha hK (fun s _ => abs_radialLogSource_le hlam hL hint hvar hmean hLz hvan s) hA

end HTGeometry
