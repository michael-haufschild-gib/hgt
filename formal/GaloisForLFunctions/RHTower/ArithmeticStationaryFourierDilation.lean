import GaloisForLFunctions.RHTower.ArithmeticStationaryFourierBudget
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueApertureMetric
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture

/-!
# Exact dilation and finite inversion of the stationary Fourier source

The literal scaled Bernoulli atom satisfies `A(s,N,d*k) = A(s,d*N,k)/d^(2 : ℕ)`.
Consequently, the finite stationary sector is the weighted multiples transform
of the first negative harmonic at integer anchors. Existing finite aperture
Möbius inversion recovers that complex profile exactly on its stationary carrier.
Its imaginary part recovers the previously defined real stationary budget.

These are source identities, with no zero premise. The final zero consequence
uses the already proved positive stationary budget to locate a positive first
harmonic. It includes critical zeros and supplies no off-line-zero exclusion.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Integer frequency dilation contributes the exact inverse-square Bernoulli weight. -/
theorem bernoulliModeWeight_mul (d : ℕ) (k : ℤ) :
    bernoulliModeWeight ((d:ℤ)*k) = bernoulliModeWeight k/(d:ℝ)^(2 : ℕ) := by
  simp only [bernoulliModeWeight, Int.cast_mul, Int.cast_natCast, mul_pow, div_div]
  congr 1
  ring

/-- Integer frequency dilation equals literal dilation of the spatial argument. -/
theorem fourier_integer_dilation (d : ℕ) (k : ℤ) (x : ℝ) :
    fourier ((d:ℤ)*k) (x : AddCircle (1:ℝ)) = fourier k ((d:ℝ)*x : AddCircle (1:ℝ)) := by
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The full complex Fourier source retains its exact power factor under dilation. -/
theorem bernoulliFourierTerm_dilation (s : ℂ) {d : ℕ} (hd : 1 ≤ d) (k : ℤ)
    {x : ℝ} (hx : 0 < x) :
    bernoulliFourierTerm ((d:ℤ)*k) s x = (d:ℂ)^s * bernoulliFourierTerm k s ((d:ℝ)*x) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hdR.ne'
  have hp : (d:ℂ)^s*(d:ℂ)^(-s-2) = 1/(d:ℂ)^(2 : ℕ) := by
    rw [← Complex.cpow_add _ _ hdC, show s+(-s-2)=-(2:ℂ) by ring,
      Complex.cpow_neg, Complex.cpow_two, one_div]
  have hm := Complex.mul_cpow_ofReal_nonneg hdR.le hx.le (-s-2)
  simp only [Complex.ofReal_natCast] at hm
  simp only [bernoulliFourierTerm, bernoulliModeWeight_mul, fourier_integer_dilation,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_mul]
  rw [hm]
  calc
    _ = ((d:ℂ)^s*(d:ℂ)^(-s-2)) *
        ((bernoulliModeWeight k:ℂ)*fourier k ((d:ℝ)*x : AddCircle (1:ℝ))*(x:ℂ)^(-s-2)) := by rw [hp]; ring
    _ = _ := by ring

/-- Positive dilation transports the literal improper integral and its Jacobian. -/
theorem integral_bernoulliFourierTerm_dilation (s : ℂ) {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (k : ℤ) :
    (∫ x in Ioi (N:ℝ), bernoulliFourierTerm ((d:ℤ)*k) s x) =
      ((d:ℂ)^s/(d:ℂ)) * ∫ x in Ioi ((d*N:ℕ):ℝ), bernoulliFourierTerm k s x := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have he : (∫ x in Ioi (N:ℝ), bernoulliFourierTerm ((d:ℤ)*k) s x) =
      ∫ x in Ioi (N:ℝ), (d:ℂ)^s*bernoulliFourierTerm k s ((d:ℝ)*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact bernoulliFourierTerm_dilation s hd k (lt_of_le_of_lt (Nat.cast_nonneg N) hx)
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi _ _ hdR]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, Nat.cast_mul,
    div_eq_mul_inv, mul_assoc]

/-- Frequency and integer anchor enter the scaled source through their product. -/
theorem scaledBernoulliFourierAtom_dilation (s : ℂ) {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (k : ℤ) :
    scaledBernoulliFourierAtom s N ((d:ℤ)*k) = scaledBernoulliFourierAtom s (d*N) k/(d:ℂ)^(2 : ℕ) := by
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hp : (d:ℂ)^(star s+1) = (d:ℂ)^(star s)*(d:ℂ) := by
    rw [Complex.cpow_add _ _ hdC, Complex.cpow_one]
  rw [scaledBernoulliFourierAtom, integral_bernoulliFourierTerm_dilation (star s) hd N k,
    scaledBernoulliFourierAtom]
  simp only [Nat.cast_mul]
  rw [Complex.natCast_mul_natCast_cpow, hp]
  field_simp

/-- The first K negative Fourier modes at a fixed integer anchor. -/
def negativeFourierSection (s : ℂ) (N K : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, scaledBernoulliFourierAtom s N (-(k:ℤ))

/-- Every finite negative-frequency section is a weighted multiples sum of the first harmonic. -/
theorem negativeFourierSection_dilation (s : ℂ) (N K : ℕ) :
    negativeFourierSection s N K =
      ∑ k ∈ Finset.Icc 1 K, scaledBernoulliFourierAtom s (k*N) (-1)/(k:ℂ)^(2 : ℕ) := by
  unfold negativeFourierSection
  apply Finset.sum_congr rfl
  intro k hk
  have h := scaledBernoulliFourierAtom_dilation s (Finset.mem_Icc.mp hk).1 N (-1)
  simpa only [mul_neg, mul_one] using h

/-- Existing finite aperture inversion recovers the literal first negative harmonic. -/
theorem negativeFourierSection_mobius_inversion (s : ℂ) (N : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℂ) *
      negativeFourierSection s (d*N) (K/d)/(d:ℂ)^(2 : ℕ)) = scaledBernoulliFourierAtom s N (-1) := by
  have h := RHTower.finiteApertureMobiusReconstruction_eq hK
    (fun k => scaledBernoulliFourierAtom s N (-(k:ℤ)))
  unfold RHTower.finiteApertureMobiusReconstruction RHTower.finiteApertureRaySum at h
  simp only [Nat.cast_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  rw [RHTower.sum_Icc_dvd_reindex d K (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)]
  unfold negativeFourierSection
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he := scaledBernoulliFourierAtom_dilation s (Finset.mem_Icc.mp hd).1 N (-(k:ℤ))
  simp only [Nat.cast_mul, mul_neg] at he ⊢
  rw [he]
  ring

/-- The full complex stationary sector, including a saddle at the anchor. -/
def stationaryComplexBudget (s : ℂ) (N : ℕ) : ℂ :=
  negativeFourierSection s N ⌊s.im/(2*Real.pi*N)⌋₊

/-- Reindex a finite negative integer interval by positive natural magnitudes. -/
theorem sum_negative_integer_interval (f : ℤ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc (-(K:ℤ)) (-1), f k) =
      ∑ k ∈ Finset.Icc 1 K, f (-(k:ℤ)) := by
  symm
  apply Finset.sum_nbij' (i := fun k : ℕ => -(k:ℤ)) (j := fun k : ℤ => (-k).toNat)
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro k hk
    simp
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro k hk
    rfl

/-- The complex stationary sector has exactly the previously defined real budget as imaginary part. -/
theorem stationaryComplexBudget_im {s : ℂ} (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (stationaryComplexBudget s N).im = stationaryFourierBudget s N := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hf := Int.natCast_floor_eq_floor (div_nonneg ht (show 0 ≤ 2*Real.pi*(N:ℝ) by positivity))
  rw [stationaryComplexBudget, negativeFourierSection, Complex.im_sum, stationaryFourierBudget,
    stationaryFourierIndices, ← hf, sum_negative_integer_interval]

/-- The exact stationary cutoff at a dilated anchor is the original cutoff divided by the dilation. -/
theorem stationary_frequency_cutoff_mul (t : ℝ) (d N : ℕ) :
    ⌊t/(2*Real.pi*(d*N))⌋₊ = ⌊t/(2*Real.pi*N)⌋₊/d := by
  rw [← Nat.floor_div_natCast]
  congr 1
  rw [div_div]
  congr 1
  ring

/-- At an active anchor, finite Möbius inversion recovers the complex first harmonic. -/
theorem stationaryComplexBudget_mobius_inversion (s : ℂ) (N : ℕ)
    (hactive : 1 ≤ ⌊s.im/(2*Real.pi*N)⌋₊) :
    (∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊, (ArithmeticFunction.moebius d : ℂ) *
      stationaryComplexBudget s (d*N)/(d:ℂ)^(2 : ℕ)) = scaledBernoulliFourierAtom s N (-1) := by
  simp only [stationaryComplexBudget, Nat.cast_mul, stationary_frequency_cutoff_mul]
  exact negativeFourierSection_mobius_inversion s N hactive

/-- The actual real stationary budgets recover the imaginary first harmonic at every active anchor. -/
theorem stationaryFourierBudget_mobius_inversion {s : ℂ} (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hactive : 1 ≤ ⌊s.im/(2*Real.pi*N)⌋₊) :
    (∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊, (ArithmeticFunction.moebius d : ℝ) *
      stationaryFourierBudget s (d*N)/(d:ℝ)^(2 : ℕ)) = (scaledBernoulliFourierAtom s N (-1)).im := by
  have h := congrArg Complex.im (stationaryComplexBudget_mobius_inversion s N hactive)
  rw [Complex.im_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  have hdN : 1 ≤ d*N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := (Finset.mem_Icc.mp hd).1; omega) (by omega))
  have he : (ArithmeticFunction.moebius d : ℂ) * stationaryComplexBudget s (d*N)/(d:ℂ)^(2 : ℕ) =
      (((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^(2 : ℕ)):ℝ) * stationaryComplexBudget s (d*N) := by
    push_cast
    ring
  rw [he]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    stationaryComplexBudget_im ht hdN]
  ring

/-- The actual complex stationary sector is a finite weighted sum over integer anchors. -/
theorem stationaryComplexBudget_dilation (s : ℂ) (N : ℕ) :
    stationaryComplexBudget s N =
      ∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊,
        scaledBernoulliFourierAtom s (d*N) (-1)/(d:ℂ)^(2 : ℕ) :=
  negativeFourierSection_dilation s N _

/-- The actual real budget retains the imaginary first-harmonic values and their inverse-square weights. -/
theorem stationaryFourierBudget_dilation {s : ℂ} (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) :
    stationaryFourierBudget s N =
      ∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊,
        (scaledBernoulliFourierAtom s (d*N) (-1)).im/(d:ℝ)^(2 : ℕ) := by
  rw [← stationaryComplexBudget_im ht hN, stationaryComplexBudget_dilation,
    Complex.im_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : scaledBernoulliFourierAtom s (d*N) (-1)/(d:ℂ)^(2 : ℕ) =
      (((1:ℝ)/(d:ℝ)^(2 : ℕ)):ℝ)*scaledBernoulliFourierAtom s (d*N) (-1) := by
    push_cast
    ring
  rw [he]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- A positive integer anchor is active exactly up to the first-frequency threshold. -/
theorem stationary_frequency_active_iff (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ⌊t/(2*Real.pi*N)⌋₊ ↔ 2*Real.pi*N ≤ t := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Nat.one_le_floor_iff, le_div_iff₀ (show 0 < 2*Real.pi*(N:ℝ) by positivity), one_mul]

/-- Beyond the first-frequency threshold the complex stationary sector is empty. -/
theorem stationaryComplexBudget_eq_zero_of_subresonant (s : ℂ)
    {N : ℕ} (hN : 1 ≤ N) (hsub : s.im < 2*Real.pi*N) :
    stationaryComplexBudget s N = 0 := by
  have hf : ⌊s.im/(2*Real.pi*N)⌋₊ = 0 := by
    have h := (stationary_frequency_active_iff s.im hN).not.mpr (not_le.mpr hsub)
    omega
  simp [stationaryComplexBudget, hf, negativeFourierSection]

/-- The literal first negative harmonic, restricted to the finite stationary carrier. -/
def stationaryFirstHarmonic (s : ℂ) (N : ℕ) : ℂ :=
  if 1 ≤ ⌊s.im/(2*Real.pi*N)⌋₊ then scaledBernoulliFourierAtom s N (-1) else 0

/-- On the stationary carrier the truncated profile equals the literal first harmonic. -/
theorem stationaryFirstHarmonic_eq_atom {s : ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hactive : 2*Real.pi*N ≤ s.im) :
    stationaryFirstHarmonic s N = scaledBernoulliFourierAtom s N (-1) := by
  simp [stationaryFirstHarmonic, (stationary_frequency_active_iff s.im hN).mpr hactive]

/-- Outside the stationary carrier the truncated profile is zero. -/
theorem stationaryFirstHarmonic_eq_zero {s : ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hsub : s.im < 2*Real.pi*N) : stationaryFirstHarmonic s N = 0 := by
  simp [stationaryFirstHarmonic, (stationary_frequency_active_iff s.im hN).not.mpr (not_le.mpr hsub)]

/-- The finite complex inverse recovers the truncated profile, including inactive anchors. -/
theorem stationaryComplexBudget_mobius_reconstruction (s : ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊,
      (ArithmeticFunction.moebius d : ℂ)*stationaryComplexBudget s (d*N)/(d:ℂ)^(2 : ℕ)) =
      stationaryFirstHarmonic s N := by
  by_cases hactive : 1 ≤ ⌊s.im/(2*Real.pi*N)⌋₊
  · simpa [stationaryFirstHarmonic, hactive] using
      stationaryComplexBudget_mobius_inversion s N hactive
  · have hf : ⌊s.im/(2*Real.pi*N)⌋₊ = 0 := by omega
    simp [stationaryFirstHarmonic, hf]

/-- The finite real inverse recovers the imaginary truncated profile, including inactive anchors. -/
theorem stationaryFourierBudget_mobius_reconstruction {s : ℂ} (ht : 0 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊,
      (ArithmeticFunction.moebius d : ℝ)*stationaryFourierBudget s (d*N)/(d:ℝ)^(2 : ℕ)) =
      (stationaryFirstHarmonic s N).im := by
  by_cases hactive : 1 ≤ ⌊s.im/(2*Real.pi*N)⌋₊
  · simpa [stationaryFirstHarmonic, hactive] using
      stationaryFourierBudget_mobius_inversion ht hN hactive
  · have hf : ⌊s.im/(2*Real.pi*N)⌋₊ = 0 := by omega
    simp [stationaryFirstHarmonic, hf]

/-- Every closed-right strip zero of height at least one requires a positive first harmonic at some retained integer anchor. -/
theorem exists_positive_first_harmonic_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    ∃ N ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi)⌋₊,
      0 < (scaledBernoulliFourierAtom s N (-1)).im := by
  have hb := stationaryFourierBudget_pos_at_closed_right_zero hs hs' ht hz
  rw [stationaryFourierBudget_dilation (by linarith) (by rfl : 1 ≤ (1:ℕ))] at hb
  simp only [Nat.cast_one, mul_one] at hb
  by_contra! hn
  have hn' : (∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi)⌋₊,
      (scaledBernoulliFourierAtom s d (-1)).im/(d:ℝ)^(2 : ℕ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro d hd
    exact div_nonpos_of_nonpos_of_nonneg (hn d hd) (sq_nonneg _)
  linarith

/-- The truncated first-harmonic profile reconstructs the complete complex stationary family. -/
theorem stationaryComplexBudget_eq_sum_firstHarmonic (s : ℂ) (N : ℕ) :
    stationaryComplexBudget s N =
      ∑ d ∈ Finset.Icc 1 ⌊s.im/(2*Real.pi*N)⌋₊,
        stationaryFirstHarmonic s (d*N)/(d:ℂ)^(2 : ℕ) := by
  rw [stationaryComplexBudget_dilation]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
  have ha : 1 ≤ ⌊s.im/(2*Real.pi*(d*N:ℕ))⌋₊ := by
    simp only [Nat.cast_mul, stationary_frequency_cutoff_mul]
    exact (Nat.one_le_div_iff hd0).mpr (Finset.mem_Icc.mp hd).2
  rw [stationaryFirstHarmonic, if_pos ha]

end RHTower.DeletionMixedRefinement
