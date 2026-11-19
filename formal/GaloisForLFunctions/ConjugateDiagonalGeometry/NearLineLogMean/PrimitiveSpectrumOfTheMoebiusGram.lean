import GaloisForLFunctions.RHTower.MobiusReciprocalPrimitiveRatio
import GaloisForLFunctions.RHTower.Sieve.GallagherReverse
import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZeroForcesALogarithmicFloor

/-!
# The signed spectrum of the critical Möbius Gram form

In the weighted Vandermonde Gram expansion of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4), Fourier support selects frequency differences.
For the logarithmic frequencies of the critical Möbius polynomial, each
distinct difference has a rational ratio and a coefficient of fixed sign.
Changing the observation window changes the multiplier on this same spectrum.
-/

noncomputable section
open Finset Complex Filter Topology MeasureTheory RHTower RHTower.Sieve
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

/-- Critical-line coefficient of the truncated Möbius Dirichlet series. -/
def coeff (n : ℕ) : ℝ := mobiusRealCoefficient n / Real.sqrt n

/-- The atom at the directed frequency `log a - log b` after reducing the ratio. -/
def atom (N a b : ℕ) : ℝ := coeff a * coeff b * primitiveCubicScaleWeight 0 N a b

private theorem coeff_mul (d a : ℕ) :
    coeff (d*a) = if Nat.Coprime d a then coeff d * coeff a else 0 := by
  unfold coeff mobiusRealCoefficient
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  split_ifs with h
  · rw [moebius_mul_of_coprime h, Int.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [moebius_mul_eq_zero_of_not_coprime h]

private theorem coeff_sq (n : ℕ) :
    coeff n ^ 2 = mobiusRealCoefficient n ^ 2 / n := by
  rw [coeff, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem scale_product (d a b : ℕ) :
    coeff (d*a)*coeff (d*b) = coeff a * coeff b *
      (if d.Coprime a ∧ d.Coprime b then mobiusRealCoefficient d ^ 2 * (d : ℝ)⁻¹ else 0) := by
  by_cases ha : d.Coprime a
  · by_cases hb : d.Coprime b
    · rw [coeff_mul d a, coeff_mul d b, if_pos ha, if_pos hb, if_pos (And.intro ha hb)]
      calc _ = coeff a * coeff b * coeff d^2 := by ring
           _ = _ := by rw [coeff_sq]; ring
    · simp [coeff_mul d b, hb]
  · simp [coeff_mul d a, ha]

/-- All dilations of a fixed directed ratio add with the same Möbius sign. -/
theorem scale_correlation (N a b : ℕ) :
    ∑ d ∈ ratioScales N a b, coeff (d*a)*coeff (d*b) = atom N a b := by
  simp only [scale_product, atom, primitiveCubicScaleWeight, sub_zero, Real.rpow_neg_one,
    Finset.mul_sum]

/-- Triangle inequality is an equality within every ratio fibre, even before
putting a spectral window on it. -/
theorem absolute_scale_correlation (N a b : ℕ) :
    ∑ d ∈ ratioScales N a b, |coeff (d*a)*coeff (d*b)| = |atom N a b| := by
  rw [atom, abs_mul, abs_of_nonneg (primitiveCubicScaleWeight_nonneg 0 N a b),
    primitiveCubicScaleWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [scale_product, abs_mul (coeff a * coeff b)]
  simp only [sub_zero, Real.rpow_neg_one]
  congr 1
  apply abs_of_nonneg
  split_ifs <;> positivity

/-- A spectral multiplier acts only on primitive log ratios. This applies to
every real kernel, including signed and discontinuous windows. -/
theorem gram_spectrum (N : ℕ) (K : ℝ → ℝ) :
    (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, coeff m * coeff n * K (Real.log m - Real.log n)) =
      K 0 * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2 / n) +
        ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 * K (Real.log q.1 - Real.log q.2) := by
  classical
  let F := fun m n : ℕ => coeff m * coeff n * K (Real.log m - Real.log n)
  have hd : ∀ m ∈ Icc 1 N, F m m = K 0 * (mobiusRealCoefficient m^2 / m) := by
    intro m _
    simp only [F, sub_self, ← sq, coeff_sq]
    ring
  have hoff : (∑ p ∈ offDiagPairs N, F p.1 p.2) =
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 * K (Real.log q.1 - Real.log q.2) := by
    rw [sum_offDiagPairs_eq_sum_ratio]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    rw [← scale_correlation, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hdm
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hdm).1).1)
    have ha0 : (q.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_Icc.mp ha).1)
    have hb0 : (q.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_Icc.mp hb).1)
    simp only [F, Nat.cast_mul, Real.log_mul hd0 ha0, Real.log_mul hd0 hb0, add_sub_add_left_eq_sub]
  rw [← hoff, sum_offDiagPairs_eq_double, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← hd m hm, add_comm, Finset.sum_erase_add _ _ hm]

/-- Exact continuous short-interval energy. Only reduced ratios at logarithmic
distance strictly below the bandwidth contribute. -/
theorem short_interval_spectrum (N : ℕ) (δ : ℝ) :
    (∫ u : ℝ, ‖logWindowSum (fun n => (coeff n : ℂ)) (Icc 1 N) δ u‖^2) =
      max δ 0 * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n ^ 2 / n) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 *
        max (δ - |Real.log q.1 - Real.log q.2|) 0 := by
  rw [integral_normSq_logWindowSum]
  simpa only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, abs_zero, sub_zero]
    using gram_spectrum N (fun x => max (δ - |x|) 0)

/-- The bandlimited weight integrates the critical polynomial to the same
finite arithmetic spectrum, including its signs. -/
theorem bandlimited_spectrum (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ w : ℝ, (FourierTransform.fourier (triC δ) w).re *
      ‖logPoly (fun n => (coeff n : ℂ)) (Icc 1 N) w‖^2) =
      δ * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n ^ 2 / n) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 *
        max (δ - |Real.log q.1 - Real.log q.2|) 0 := by
  rw [← gallagher_identity _ _ hδ, short_interval_spectrum, max_eq_left hδ.le]

/-- Short-window energy as a function of the physical logarithmic bandwidth. -/
def bandEnergy (N : ℕ) (δ : ℝ) : ℝ :=
  ∫ u : ℝ, ‖logWindowSum (fun n => (coeff n : ℂ)) (Icc 1 N) δ u‖^2

/-- On the inverse-length scale the Möbius energy is exactly diagonal. -/
theorem bandEnergy_diagonal {N : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hcut : δ ≤ (N : ℝ)⁻¹) :
    bandEnergy N δ = δ * ∑ n ∈ Icc 1 N, mobiusRealCoefficient n ^ 2 / n := by
  rw [bandEnergy, short_interval_spectrum, max_eq_left hδ]
  refine add_eq_left.mpr (sum_eq_zero fun q hq => ?_)
  obtain ⟨hq', _, hne⟩ := mem_filter.mp hq
  obtain ⟨ha, hb⟩ := mem_product.mp hq'
  have h := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le
    (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 hne (mem_Icc.mp ha).2 (mem_Icc.mp hb).2
  rw [max_eq_right (sub_nonpos.mpr (hcut.trans h)), mul_zero]

private theorem hinge_difference (y : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    max (y+h) 0 - 2*max y 0 + max (y-h) 0 = max (h-|y|) 0 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [max_eq_right hy, max_eq_right (by linarith : y-h ≤ 0), abs_of_nonpos hy,
      sub_neg_eq_add, add_comm h y]
    ring
  rw [max_eq_left hy.le, max_eq_left (by linarith : 0 ≤ y+h), abs_of_nonneg hy.le]
  rcases le_or_gt h y with he | he
  · rw [max_eq_left (sub_nonneg.mpr he), max_eq_right (sub_nonpos.mpr he)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr he.le), max_eq_left (sub_nonneg.mpr he.le)]
    ring

/-- Second differences of the observed energy localize the signed spectrum
in a movable triangular window centered at `x`. -/
theorem bandEnergy_second_difference (N : ℕ) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    bandEnergy N (x+h) - 2*bandEnergy N x + bandEnergy N (x-h) =
      max (h-|x|) 0 * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n ^ 2 / n) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 *
        max (h-abs (x-|Real.log q.1-Real.log q.2|)) 0 := by
  simp only [bandEnergy, short_interval_spectrum]
  have shifted (g : ℝ) : max (x+h-g) 0 - 2*max (x-g) 0 + max (x-h-g) 0 =
      max (h-|x-g|) 0 := by
    simpa only [show x-g+h=x+h-g by ring, show x-g-h=x-h-g by ring]
      using hinge_difference (x-g) hh
  rw [← hinge_difference x hh]
  simp_rw [← shifted, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intros; ring, ← Finset.mul_sum]
  ring

/-- As the bandwidth probe narrows, its normalized second difference is
eventually exactly the signed mass at that distance. This recovers the
spectrum from short-window energy measurements alone. -/
theorem recover_band_atom (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (bandEnergy N (x+h) - 2*bandEnergy N x + bandEnergy N (x-h))/h =
        ∑ q ∈ (primitiveRatioPairs N).filter (fun q =>
          |Real.log q.1-Real.log q.2| = x), atom N q.1 q.2 := by
  classical
  have hlocal (g : ℝ) : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      max (h-|x-g|) 0 = if g=x then h else 0 := by
    by_cases hg : g = x
    · subst g
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp [hh.le]
    · have hp : 0 < |x-g| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hg))
      filter_upwards [(gt_mem_nhds hp).filter_mono nhdsWithin_le_nhds] with h hh
      rw [if_neg hg, max_eq_right (sub_nonpos.mpr (le_of_lt hh))]
  have hj := (Filter.eventually_all_finset (primitiveRatioPairs N)).mpr
    (fun q _ => hlocal |Real.log q.1-Real.log q.2|)
  filter_upwards [hj, hlocal 0, self_mem_nhdsWithin] with h hq h0 (hh : 0 < h)
  rw [bandEnergy_second_difference N x hh.le]
  simp only [sub_zero, if_neg hx.ne] at h0
  rw [h0, zero_mul, zero_add, div_eq_iff hh.ne']
  rw [sum_filter, sum_mul]
  apply sum_congr rfl
  intro q hmem
  rw [hq q hmem]
  split_ifs <;> ring

private theorem frequency_gap {N a b c d : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hc : c ∈ Icc 1 N) (hd : d ∈ Icc 1 N) (hne : a*d ≠ b*c) :
    ((N:ℝ)^2)⁻¹ ≤ |(Real.log a-Real.log b)-(Real.log c-Real.log d)| := by
  have hdif := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le
    (Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hd).1)
    (Nat.mul_pos (mem_Icc.mp hb).1 (mem_Icc.mp hc).1) hne
    (Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hd).2)
    (Nat.mul_le_mul (mem_Icc.mp hb).2 (mem_Icc.mp hc).2)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (mem_Icc.mp ha).1.ne') (by exact_mod_cast (mem_Icc.mp hd).1.ne'),
    Real.log_mul (by exact_mod_cast (mem_Icc.mp hb).1.ne') (by exact_mod_cast (mem_Icc.mp hc).1.ne')] at hdif
  rw [sq, show (Real.log a-Real.log b)-(Real.log c-Real.log d) =
    (Real.log a+Real.log d)-(Real.log b+Real.log c) by ring]
  exact hdif

private theorem cross_unique {a b c d : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hcd : c.Coprime d) (he : a*d=b*c) : a=c ∧ b=d := by
  have hac : a ∣ c := hab.dvd_mul_right.mp (by rw [mul_comm c b, ← he]; exact dvd_mul_right _ _)
  have hca : c ∣ a := hcd.dvd_mul_right.mp (by rw [he]; exact dvd_mul_left _ _)
  have h := Nat.dvd_antisymm hac hca
  subst c
  rw [mul_comm b a] at he
  exact ⟨rfl, (Nat.eq_of_mul_eq_mul_left ha he).symm⟩

private theorem atom_comm (N a b : ℕ) : atom N a b = atom N b a := by
  have hscale : ratioScales N a b = ratioScales N b a := by
    ext d
    simp only [ratioScales, mem_filter]
    tauto
  rw [atom, atom, mul_comm (coeff a), primitiveCubicScaleWeight, primitiveCubicScaleWeight, hscale]
  congr 1
  exact sum_congr rfl fun d _ => by rw [and_comm (d.Coprime a)]

/-- Three energy measurements isolate each individual reduced rational
frequency. The same resolution works for every ratio at cutoff N. -/
theorem read_primitive_ratio {N a b : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hab : a.Coprime b) (hba : b < a) {h : ℝ} (hh : 0 < h) (hres : h ≤ ((N:ℝ)^2)⁻¹) :
    let x := Real.log a-Real.log b
    (bandEnergy N (x+h)-2*bandEnergy N x+bandEnergy N (x-h))/h = 2*atom N a b := by
  classical
  intro x
  have hx : 0 < x := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast (mem_Icc.mp hb).1)
    (by exact_mod_cast hba))
  have hN := (mem_Icc.mp ha).1.trans (mem_Icc.mp ha).2
  have hunit : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl,hN⟩
  have hdiag := frequency_gap ha hb hunit hunit (by simpa using hba.ne')
  have hdx : h ≤ |x| := hres.trans (by simpa only [sub_self, sub_zero] using hdiag)
  have hpair : (a,b) ∈ primitiveRatioPairs N :=
    mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab,hba.ne'⟩
  have hrev : (b,a) ∈ primitiveRatioPairs N :=
    mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,hab.symm,hba.ne⟩
  have hne : (a,b) ≠ (b,a) := fun he => hba.ne' (congrArg Prod.fst he)
  have isolate {c d : ℕ} (hq : (c,d) ∈ primitiveRatioPairs N)
      (h1 : (c,d) ≠ (a,b)) (h2 : (c,d) ≠ (b,a)) :
      h ≤ |x-|Real.log c-Real.log d|| := by
    obtain ⟨hprod,hcd,_⟩ := mem_filter.mp hq
    obtain ⟨hc,hd⟩ := mem_product.mp hprod
    rcases le_or_gt 0 (Real.log c-Real.log d) with hg | hg
    · rw [abs_of_nonneg hg]
      apply hres.trans (frequency_gap ha hb hc hd ?_)
      intro he
      obtain ⟨rfl,rfl⟩ := cross_unique (mem_Icc.mp ha).1 hab hcd he
      exact h1 rfl
    · rw [abs_of_nonpos hg.le, neg_sub]
      apply hres.trans (frequency_gap ha hb hd hc ?_)
      intro he
      obtain ⟨rfl,rfl⟩ := cross_unique (mem_Icc.mp ha).1 hab hcd.symm he
      exact h2 rfl
  rw [bandEnergy_second_difference N x hh.le, max_eq_right (sub_nonpos.mpr hdx),
    zero_mul, zero_add, div_eq_iff hh.ne']
  -- Only the two orientations of the selected fraction survive.
  rw [← add_sum_erase _ _ hpair,
    ← add_sum_erase _ _ (mem_erase.mpr ⟨hne.symm,hrev⟩)]
  have hrest : ∑ q ∈ ((primitiveRatioPairs N).erase (a,b)).erase (b,a),
      atom N q.1 q.2 * max (h-|x-|Real.log q.1-Real.log q.2||) 0 = 0 := by
    apply sum_eq_zero
    rintro ⟨c,d⟩ hq
    have hq1 := mem_erase.mp hq
    have hq2 := mem_erase.mp hq1.2
    rw [max_eq_right (sub_nonpos.mpr (isolate hq2.2 hq2.1 hq1.1)), mul_zero]
  rw [hrest, add_zero]
  change atom N a b * max (h-|x-|x||) 0 +
    atom N b a * max (h-|x-|Real.log b-Real.log a||) 0 = _
  rw [abs_sub_comm (Real.log b), abs_of_pos hx, sub_self, abs_zero, sub_zero,
    max_eq_left hh.le, atom_comm N b a]
  ring

private theorem one_le_fibre_weight {N a b : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) :
    1 ≤ primitiveCubicScaleWeight 0 N a b := by
  have h1 : 1 ∈ ratioScales N a b := mem_filter.mpr ⟨mem_Icc.mpr
    ⟨le_rfl,(mem_Icc.mp ha).1.trans (mem_Icc.mp ha).2⟩, by simpa using
      And.intro (mem_Icc.mp ha).2 (mem_Icc.mp hb).2⟩
  unfold primitiveCubicScaleWeight
  have hn (d : ℕ) (hd : d ∈ ratioScales N a b) : 0 ≤
      (if Nat.Coprime d a ∧ Nat.Coprime d b
       then mobiusRealCoefficient d ^ 2 * (d : ℝ) ^ (-1 - (0:ℝ)) else 0) := by
    split_ifs <;> positivity
  simpa [mobiusRealCoefficient] using Finset.single_le_sum hn h1

/-- At a primitive ratio the bandwidth test vanishes precisely when a
numerator or a denominator is not squarefree. Dilation cannot erase
an occupied ratio because the unit dilation contributes weight one. -/
theorem ratio_readout_ne_zero_iff {N a b : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hab : a.Coprime b) (hba : b < a) {h : ℝ} (hh : 0 < h) (hres : h ≤ ((N:ℝ)^2)⁻¹) :
    let x := Real.log a-Real.log b
    (bandEnergy N (x+h)-2*bandEnergy N x+bandEnergy N (x-h))/h ≠ 0 ↔
      Squarefree a ∧ Squarefree b := by
  intro x
  have ha0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (mem_Icc.mp ha).1)).ne'
  have hb0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (mem_Icc.mp hb).1)).ne'
  have hw := (lt_of_lt_of_le zero_lt_one (one_le_fibre_weight ha hb)).ne'
  change (_ ≠ 0) ↔ _
  rw [read_primitive_ratio ha hb hab hba hh hres]
  simp [atom, coeff, mobiusRealCoefficient, ha0, hb0, hw,
    ← ArithmeticFunction.moebius_ne_zero_iff_squarefree]

open GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem critical_poly (N : ℕ) (t : ℝ) :
    moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t) = _root_.HTGeometry.genPoly (fun n => (coeff n : ℂ))
      (fun n => -Real.log n) (Icc 1 N) t := by
  unfold moebiusPoly edPoly _root_.HTGeometry.genPoly
  apply Finset.sum_congr rfl
  intro n hn
  have h : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have hn' : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
  have hscale : ((Real.sqrt n : ℝ) : ℂ)⁻¹ = cexp (((Real.log n : ℝ) : ℂ) * (-1/2)) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg h.le, Real.rpow_def_of_pos h, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_log h.le, MultiscaleMollifiedZetaField.linePoint]
  simp only [coeff, mobiusRealCoefficient, mobCoeff, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_intCast, Complex.ofReal_inv, hscale, Complex.ofReal_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Instantaneous power of the literal critical Möbius polynomial as a cosine
series. Its frequencies and signed amplitudes work for every time window. -/
theorem critical_power_spectrum (N : ℕ) (t : ℝ) :
    ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2 =
      (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2 / n) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 *
        Real.cos ((Real.log q.1 - Real.log q.2)*t) := by
  have hg := congrArg Complex.re (_root_.HTGeometry.genPoly_mul_conj
    (fun n => (coeff n : ℂ)) (fun n => -Real.log n) (Icc 1 N) t)
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, ← critical_poly] at hg
  simp only [Complex.re_sum, Complex.conj_ofReal, ← Complex.ofReal_mul] at hg
  rw [hg]
  have hterm (a b : ℕ) :
      (((coeff b * coeff a : ℝ) : ℂ) *
        cexp (I * (((-Real.log b - -Real.log a : ℝ) : ℂ) * t))).re =
      coeff a * coeff b * Real.cos ((Real.log a - Real.log b)*t) := by
    rw [show I * (((-Real.log b - -Real.log a : ℝ) : ℂ) * t) =
      ((((Real.log a - Real.log b)*t : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm (coeff b)]
  calc _ = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, coeff a * coeff b *
          Real.cos ((Real.log a-Real.log b)*t) := by
         apply Finset.sum_congr rfl
         intro a _
         apply Finset.sum_congr rfl
         intro b _
         simpa only [← Complex.ofReal_mul] using hterm a b
       _ = _ := by simpa using gram_spectrum N (fun x => Real.cos (x*t))

/-- Exact integral on the sharp interval, retaining the contribution from each
nonzero log ratio even when two frequencies are arbitrarily close. -/
theorem sharp_interval_spectrum (N : ℕ) (A B : ℝ) :
    (∫ t in A..B, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2) =
      (B-A) * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2 / n) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 *
        (∫ t in A..B, Real.cos ((Real.log q.1 - Real.log q.2)*t)) := by
  simp_rw [critical_power_spectrum]
  have hI (q : ℕ × ℕ) : IntervalIntegrable
      (fun t => atom N q.1 q.2 * Real.cos ((Real.log q.1 - Real.log q.2)*t)) volume A B :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsum : IntervalIntegrable (fun t => ∑ q ∈ primitiveRatioPairs N,
      atom N q.1 q.2 * Real.cos ((Real.log q.1 - Real.log q.2)*t)) volume A B := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum (primitiveRatioPairs N) (fun q _ => hI q)
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
    intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_finsetSum
      (fun q _ => hI q)]
  congr 1
  exact Finset.sum_congr rfl fun q _ => intervalIntegral.integral_const_mul _ _

#print axioms scale_correlation
#print axioms absolute_scale_correlation
#print axioms gram_spectrum
#print axioms short_interval_spectrum
#print axioms bandlimited_spectrum
#print axioms bandEnergy_diagonal
#print axioms bandEnergy_second_difference
#print axioms recover_band_atom
#print axioms ratio_readout_ne_zero_iff
#print axioms read_primitive_ratio
#print axioms critical_power_spectrum
#print axioms sharp_interval_spectrum
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
