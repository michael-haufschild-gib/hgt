import GaloisForLFunctions.WindowTowerOfSpecZ.RationalHeckeGraphsDetermineWindowPositivity
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily
import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.ContinuumMatrixSpectralHankel
import Mathlib.Analysis.Matrix.Order
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Positive prime multipliers lower Tate dimension

Ratios of Jordan coefficients are products of positive prime-valuation
kernels. Their Gram decompositions preserve rational Hecke positivity.
The diagonal part of the multiplier gives a strict interior margin.
-/

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexConjugate MatrixOrder

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open ArithmeticDegenerationTheory CohomologyOfWindowsOfSpecZ

/-- A Gram multiplier with diagonal `1−ε` and prescribed values on Hecke
edges transfers positivity with the explicit diagonal margin `ε`. -/
theorem rationalHeckeForm_ge_of_gram_multiplier {ι : Type*} [Fintype ι]
    (N : ℕ) (c m : ℕ → ℝ) (S : Finset ℚ) (F : ι → ℚ → ℝ) (ε : ℝ)
    (hdiag : ∀ r ∈ S, ∑ i, F i r ^ 2 = 1 - ε)
    (hedge : ∀ n ∈ Finset.Icc 2 N, ∀ r ∈ S, ∀ s ∈ S,
      (s : ℝ) = n * r → ∑ i, F i r * F i s = m n)
    (hpos : ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm N c S y) (y : ℚ → ℝ) :
    ε * (∑ r ∈ S, y r ^ 2) ≤ rationalHeckeForm N (fun n => c n * m n) S y := by
  classical
  have hdiagSum : (∑ i, ∑ r ∈ S, (y r * F i r) ^ 2) =
      (1 - ε) * ∑ r ∈ S, y r ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    calc
      (∑ i, (y r * F i r) ^ 2) = y r ^ 2 * ∑ i, F i r ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = (1 - ε) * y r ^ 2 := by rw [hdiag r hr]; ring
  have hedgeSum : ∀ n ∈ Finset.Icc 2 N,
      (∑ i, ∑ r ∈ S, ∑ s ∈ S,
        if (s : ℝ) = n * r then (y r * F i r) * (y s * F i s) else 0) =
      m n * ∑ r ∈ S, ∑ s ∈ S,
        if (s : ℝ) = n * r then y r * y s else 0 := by
    intro n hn
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases he : (s : ℝ) = n * r
    · simp only [he, if_true]
      calc
        (∑ i, (y r * F i r) * (y s * F i s)) =
          (y r * y s) * ∑ i, F i r * F i s := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = m n * (y r * y s) := by rw [hedge n hn r hr s hs he]; ring
    · simp only [he, if_false, Finset.sum_const_zero, mul_zero]
  have hsum : (∑ i, rationalHeckeForm N c S (fun r => y r * F i r)) =
      rationalHeckeForm N (fun n => c n * m n) S y - ε * ∑ r ∈ S, y r ^ 2 := by
    unfold rationalHeckeForm
    rw [Finset.sum_add_distrib, hdiagSum, Finset.sum_comm]
    have he : (∑ n ∈ Finset.Icc 2 N, ∑ i,
        c n * ∑ r ∈ S, ∑ s ∈ S,
          if (s : ℝ) = n * r then (y r * F i r) * (y s * F i s) else 0) =
        ∑ n ∈ Finset.Icc 2 N, (c n * m n) * ∑ r ∈ S, ∑ s ∈ S,
          if (s : ℝ) = n * r then y r * y s else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.mul_sum, hedgeSum n hn]
      ring
    rw [he]
    ring
  have hnn : 0 ≤ ∑ i, rationalHeckeForm N c S (fun r => y r * F i r) :=
    Finset.sum_nonneg fun i _ => hpos _
  rw [hsum] at hnn
  exact sub_nonneg.mp hnn

/-- Powers of an integer distance form a positive semidefinite kernel.
Circle Poisson moments express it as the sum of two real Gram matrices. -/
theorem integerDistanceKernel_posSemidef {ι : Type*} [Fintype ι]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (v : ι → ℤ) :
    Matrix.PosSemidef (fun i j => r ^ (v i - v j).natAbs) := by
  rcases eq_or_lt_of_le hr1 with rfl | hr1
  · simp only [one_pow]
    change (Matrix.of (fun (_ : ι) (_ : ι) => (1 : ℝ))).PosSemidef
    have he : (Matrix.of (fun (_ : ι) (_ : ι) => (1 : ℝ))) =
        (Matrix.of (fun (_ : Unit) (_ : ι) => (1 : ℝ)))ᴴ *
          (Matrix.of (fun (_ : Unit) (_ : ι) => (1 : ℝ))) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
        one_mul, Fintype.sum_unique]
    rw [he]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · let a : HTGeometry.CirclePoissonParameter := ⟨(r : ℂ), by
      simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr0] using hr1⟩
    let μ : Measure UnitAddCircle :=
      (HTGeometry.addCirclePoissonProbabilityMeasure a : Measure UnitAddCircle)
    have hmoment (q : ℤ) : (∫ z, (fourier q z).re ∂μ) = r ^ q.natAbs := by
      have hi : Integrable (fun z : UnitAddCircle => fourier q z) μ :=
        (fourier q).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hRe : (∫ z, (fourier q z).re ∂μ) = (∫ z, fourier q z ∂μ).re :=
        Complex.reCLM.integral_comp_comm hi
      rw [hRe, HTGeometry.integral_fourier_addCirclePoissonProbabilityMeasure]
      cases q <;> simp [a, ← Complex.ofReal_pow]
    have hprodRe (i j : ι) : Integrable
        (fun z : UnitAddCircle => (fourier (v i) z).re * (fourier (v j) z).re) μ := by
      have hc : Continuous (fun z : UnitAddCircle =>
          (fourier (v i) z).re * (fourier (v j) z).re) :=
        (Complex.continuous_re.comp (fourier (v i)).continuous).mul
          (Complex.continuous_re.comp (fourier (v j)).continuous)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hprodIm (i j : ι) : Integrable
        (fun z : UnitAddCircle => (fourier (v i) z).im * (fourier (v j) z).im) μ := by
      have hc : Continuous (fun z : UnitAddCircle =>
          (fourier (v i) z).im * (fourier (v j) z).im) :=
        (Complex.continuous_im.comp (fourier (v i)).continuous).mul
          (Complex.continuous_im.comp (fourier (v j)).continuous)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hR := _root_.HTGeometry.integralFeatureGram_posSemidef μ
      (fun i z => (fourier (v i) z).re) hprodRe
    have hI := _root_.HTGeometry.integralFeatureGram_posSemidef μ
      (fun i z => (fourier (v i) z).im) hprodIm
    have he : (fun i j => r ^ (v i - v j).natAbs) =
        _root_.HTGeometry.integralFeatureGram μ (fun i z => (fourier (v i) z).re) +
        _root_.HTGeometry.integralFeatureGram μ (fun i z => (fourier (v i) z).im) := by
      funext i j
      rw [Matrix.add_apply, _root_.HTGeometry.integralFeatureGram,
        _root_.HTGeometry.integralFeatureGram, ← integral_add (hprodRe i j) (hprodIm i j),
        ← hmoment]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (fourier (v i - v j) z).re =
          (fourier (v i) z).re * (fourier (v j) z).re +
            (fourier (v i) z).im * (fourier (v j) z).im
        rw [sub_eq_add_neg, fourier_add, fourier_neg]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    rw [he]
    exact hR.add hI

private theorem exists_realGram_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℝ} (hK : K.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, ∀ i j, ∑ l, B l i * B l j = K i j := by
  let B := CFC.sqrt K
  have hB : Bᴴ = B := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg K).star_eq
  have hBB : B * B = K := by
    simpa only [pow_two] using CFC.sq_sqrt K (Matrix.nonneg_iff_posSemidef.mpr hK)
  refine ⟨B, fun i j => ?_⟩
  have hs (l : ι) : B l i = B i l := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M i l) hB
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
  calc
    (∑ l, B l i * B l j) = (B * B) i j := by
      simp only [Matrix.mul_apply, hs]
    _ = K i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hBB

/-- A positive semidefinite matrix whose entries depend only on each Hecke
ratio acts as a positivity-preserving coefficient multiplier. -/
theorem rationalHeckeForm_ge_of_psd_multiplier
    (N : ℕ) (c m : ℕ → ℝ) (S : Finset ℚ) (K : Matrix S S ℝ) (ε : ℝ)
    (hK : K.PosSemidef) (hdiag : ∀ r, K r r = 1 - ε)
    (hedge : ∀ n ∈ Finset.Icc 2 N, ∀ r s : S,
      (s : ℚ) = n * (r : ℚ) → K r s = m n)
    (hpos : ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm N c S y) (y : ℚ → ℝ) :
    ε * (∑ r ∈ S, y r ^ 2) ≤ rationalHeckeForm N (fun n => c n * m n) S y := by
  classical
  obtain ⟨B, hB⟩ := exists_realGram_of_posSemidef hK
  let F : S → ℚ → ℝ := fun i r => if hr : r ∈ S then B i ⟨r, hr⟩ else 0
  apply rationalHeckeForm_ge_of_gram_multiplier N c m S F ε ?_ ?_ hpos y
  · intro r hr
    simp only [F, dif_pos hr, pow_two]
    exact (hB ⟨r, hr⟩ ⟨r, hr⟩).trans (hdiag ⟨r, hr⟩)
  · intro n hn r hr s hs he
    simp only [F, dif_pos hr, dif_pos hs]
    apply (hB ⟨r, hr⟩ ⟨s, hs⟩).trans
    apply hedge n hn
    exact_mod_cast he

/-- Equality of integer labels is a positive kernel, obtained by pulling
back the identity matrix on the integers. -/
theorem integerEqualityKernel_posSemidef {ι : Type*} (v : ι → ℤ) :
    Matrix.PosSemidef (fun i j => if v i = v j then (1 : ℝ) else 0) := by
  have he : (fun i j => if v i = v j then (1 : ℝ) else 0) =
      (1 : Matrix ℤ ℤ ℝ).submatrix v v := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
  rw [he]
  exact (Matrix.PosSemidef.one : (1 : Matrix ℤ ℤ ℝ).PosSemidef).submatrix v

/-- A convex mixture of Poisson correlations and equality of valuations. -/
def dampedIntegerKernel (ρ t : ℝ) (a b : ℤ) : ℝ :=
  ρ * t ^ (a - b).natAbs + (1 - ρ) * if a = b then 1 else 0

theorem dampedIntegerKernel_posSemidef {ι : Type*} [Fintype ι]
    {ρ t : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : ι → ℤ) : Matrix.PosSemidef (fun i j => dampedIntegerKernel ρ t (v i) (v j)) := by
  exact (integerDistanceKernel_posSemidef ht0 ht1 v |>.smul hρ0).add
    (integerEqualityKernel_posSemidef v |>.smul (sub_nonneg.mpr hρ1))

theorem dampedIntegerKernel_self (ρ t : ℝ) (a : ℤ) :
    dampedIntegerKernel ρ t a a = 1 := by
  simp only [dampedIntegerKernel, sub_self, Int.natAbs_zero, pow_zero, mul_one, if_true]
  ring

/-- Entrywise products preserve positive semidefiniteness. -/
theorem finiteKernelProduct_posSemidef {ι π : Type*} [Fintype ι]
    (P : Finset π) (K : π → Matrix ι ι ℝ) (hK : ∀ p ∈ P, (K p).PosSemidef) :
    Matrix.PosSemidef (fun i j => ∏ p ∈ P, K p i j) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, one_pow] using
      integerDistanceKernel_posSemidef (r := 1) (by norm_num) le_rfl (fun _ : ι => 0)
  | @insert p P hp ih =>
    have he : (fun i j => ∏ q ∈ insert p P, K q i j) =
        (K p).hadamard (fun i j => ∏ q ∈ P, K q i j) := by
      ext i j
      simp only [Finset.prod_insert hp, Matrix.hadamard_apply]
    rw [he]
    exact (hK p (Finset.mem_insert_self p P)).hadamard
      (ih fun q hq => hK q (Finset.mem_insert_of_mem hq))

/-- In a product of sums of positive kernels, removing the product of the
second summands leaves a positive kernel. This retains a diagonal margin. -/
theorem finiteKernelProduct_sub_posSemidef {ι π : Type*} [Fintype ι]
    (P : Finset π) (U V : π → Matrix ι ι ℝ)
    (hU : ∀ p ∈ P, (U p).PosSemidef) (hV : ∀ p ∈ P, (V p).PosSemidef) :
    Matrix.PosSemidef (fun i j => (∏ p ∈ P, (U p i j + V p i j)) -
      ∏ p ∈ P, V p i j) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | @insert p P hp ih =>
    have hU' : ∀ q ∈ P, (U q).PosSemidef :=
      fun q hq => hU q (Finset.mem_insert_of_mem hq)
    have hV' : ∀ q ∈ P, (V q).PosSemidef :=
      fun q hq => hV q (Finset.mem_insert_of_mem hq)
    have htot := finiteKernelProduct_posSemidef P (fun q => U q + V q)
      (fun q hq => (hU' q hq).add (hV' q hq))
    have he : (fun i j => (∏ q ∈ insert p P, (U q i j + V q i j)) -
        ∏ q ∈ insert p P, V q i j) =
        (U p).hadamard (fun i j => ∏ q ∈ P, (U q + V q) i j) +
          (V p).hadamard (fun i j => (∏ q ∈ P, (U q i j + V q i j)) -
            ∏ q ∈ P, V q i j) := by
      ext i j
      simp only [Finset.prod_insert hp, Matrix.add_apply, Matrix.hadamard_apply]
      ring
    rw [he]
    exact ((hU p (Finset.mem_insert_self p P)).hadamard htot).add
      ((hV p (Finset.mem_insert_self p P)).hadamard (ih hU' hV'))

/-- The Poisson weight in a ratio of positive-dimensional Jordan factors. -/
def jordanPrimeMixture (X Y : ℝ) : ℝ := (X - 1) * Y / ((Y - 1) * X)

theorem jordanPrimeMixture_bounds {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y)
    (hY : 1 < Y) : 0 ≤ jordanPrimeMixture X Y ∧ jordanPrimeMixture X Y ≤ 1 := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hd : 0 < (Y - 1) * X := mul_pos (sub_pos.mpr hY) hX0
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hX) (zero_lt_one.trans hY).le) hd.le
  · rw [jordanPrimeMixture, div_le_iff₀ hd]
    nlinarith only [hXY]

theorem jordanPrimeMixture_lt_one {X Y : ℝ} (hX : 1 ≤ X) (hXY : X < Y) :
    jordanPrimeMixture X Y < 1 := by
  have hd : 0 < (Y - 1) * X :=
    mul_pos (sub_pos.mpr (hX.trans_lt hXY)) (zero_lt_one.trans_le hX)
  rw [jordanPrimeMixture, div_lt_iff₀ hd]
  nlinarith only [hXY]

/-- The nonzero valuation coefficients are exactly the Jordan prime-power ratios. -/
theorem jordanPrimeMixture_pow {X Y : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (hY1 : Y - 1 ≠ 0) {a : ℕ} (ha : 1 ≤ a) :
    jordanPrimeMixture X Y * (X / Y) ^ a =
      (X ^ (a - 1) * (X - 1)) / (Y ^ (a - 1) * (Y - 1)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ, div_pow, jordanPrimeMixture]
  field_simp [hX, hY, hY1]

/-- The prime factors that can occur in an active integer ratio. -/
def tateActivePrimes (N : ℕ) : Finset ℕ := (Finset.Icc 2 N).filter Nat.Prime

theorem primeFactors_subset_tateActivePrimes {n N : ℕ} (hn : n ≤ N) :
    n.primeFactors ⊆ tateActivePrimes N := by
  intro p hp
  obtain ⟨hp, hpn, hn0⟩ := Nat.mem_primeFactors.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hp.two_le, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans hn⟩, hp⟩

/-- Jordan's Euler factors can be multiplied over all active primes;
the additional prime factors have exponent zero and contribute one. -/
theorem jordanTotient_eq_prod_activePrimes (k : ℝ) {n N : ℕ}
    (hn0 : n ≠ 0) (hn : n ≤ N) :
    jordanTotient k n = ∏ p ∈ tateActivePrimes N,
      jordanTotient k (p ^ padicValNat p n) := by
  have h := (isMultiplicative_jordanFun k).multiplicative_factorization (jordanFun k) hn0
  simp only [jordanFun_apply, Finsupp.prod, Nat.support_factorization] at h
  rw [h]
  calc
    (∏ p ∈ n.primeFactors, jordanTotient k (p ^ n.factorization p)) =
        ∏ p ∈ n.primeFactors, jordanTotient k (p ^ padicValNat p n) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_def n (Nat.mem_primeFactors.mp hp).1]
    _ = ∏ p ∈ tateActivePrimes N, jordanTotient k (p ^ padicValNat p n) := by
      apply Finset.prod_subset (primeFactors_subset_tateActivePrimes hn)
      intro p hp hpn
      have hpprime := (Finset.mem_filter.mp hp).2
      have hndvd : ¬p ∣ n := fun hdiv => hpn (Nat.mem_primeFactors.mpr ⟨hpprime, hdiv, hn0⟩)
      rw [padicValNat.eq_zero_of_not_dvd hndvd, pow_zero, jordanTotient_one]

/-- The scalar prime-power multiplier, normalized to one at exponent zero. -/
def tatePrimeRatio (k K : ℝ) (p a : ℕ) : ℝ :=
  if a = 0 then 1 else jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K) *
    ((p : ℝ) ^ k / (p : ℝ) ^ K) ^ a

theorem jordanTotient_mul_tatePrimeRatio {p : ℕ} (hp : p.Prime)
    {K : ℝ} (hK : 0 < K) (k : ℝ) (a : ℕ) :
    jordanTotient K (p ^ a) * tatePrimeRatio k K p a = jordanTotient k (p ^ a) := by
  by_cases ha : a = 0
  · simp only [ha, pow_zero, jordanTotient_one, tatePrimeRatio, if_true, mul_one]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hY : 1 < (p : ℝ) ^ K := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hK
    rw [tatePrimeRatio, if_neg ha,
      jordanPrimeMixture_pow (Real.rpow_pos_of_pos hp0 k).ne'
        (Real.rpow_pos_of_pos hp0 K).ne' (sub_pos.mpr hY).ne' ha1,
      jordanTotient_prime_pow hp K ha1, jordanTotient_prime_pow hp k ha1,
      Real.rpow_mul_natCast hp0.le, Real.rpow_mul_natCast hp0.le]
    exact mul_div_cancel₀ _ (mul_ne_zero
      (pow_ne_zero _ (Real.rpow_pos_of_pos hp0 K).ne') (sub_pos.mpr hY).ne')

def tateDimensionMultiplier (N : ℕ) (k K : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ tateActivePrimes N, tatePrimeRatio k K p (padicValNat p n)

theorem jordanTotient_mul_tateDimensionMultiplier {N n : ℕ} (hn0 : n ≠ 0)
    (hn : n ≤ N) {K : ℝ} (hK : 0 < K) (k : ℝ) :
    jordanTotient K n * tateDimensionMultiplier N k K n = jordanTotient k n := by
  rw [jordanTotient_eq_prod_activePrimes K hn0 hn,
    jordanTotient_eq_prod_activePrimes k hn0 hn, tateDimensionMultiplier,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact jordanTotient_mul_tatePrimeRatio (Finset.mem_filter.mp hp).2 hK k _

private theorem padicValRat_edge_natAbs {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    {r s : ℚ} (hr : r ≠ 0) (he : s = n * r) :
    (padicValRat p r - padicValRat p s).natAbs = padicValNat p n := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [he, padicValRat.mul (by exact_mod_cast hn) hr, padicValRat.of_nat]
  have heq : padicValRat p r - ((padicValNat p n : ℤ) + padicValRat p r) =
      -(padicValNat p n : ℤ) := by omega
  rw [heq, Int.natAbs_neg, Int.natAbs_natCast]

theorem dampedIntegerKernel_eq_tatePrimeRatio (k K : ℝ) (p : ℕ) (a b : ℤ) :
    dampedIntegerKernel (jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K))
      ((p : ℝ) ^ k / (p : ℝ) ^ K) a b = tatePrimeRatio k K p (a - b).natAbs := by
  by_cases hab : a = b
  · subst b
    rw [dampedIntegerKernel_self]
    simp only [tatePrimeRatio, sub_self, Int.natAbs_zero, if_true]
  · have hn : (a - b).natAbs ≠ 0 := by
      intro hzero
      exact hab (sub_eq_zero.mp (Int.natAbs_eq_zero.mp hzero))
    simp only [dampedIntegerKernel, tatePrimeRatio, if_neg hab, if_neg hn, mul_zero, add_zero]

/-- The product prime-valuation kernel realizes the ratio of Jordan coefficients. -/
def tateDimensionKernel (N : ℕ) (k K : ℝ) (r s : ℚ) : ℝ :=
  ∏ p ∈ tateActivePrimes N,
    dampedIntegerKernel (jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K))
      ((p : ℝ) ^ k / (p : ℝ) ^ K) (padicValRat p r) (padicValRat p s)

theorem tateDimensionKernel_self (N : ℕ) (k K : ℝ) (r : ℚ) :
    tateDimensionKernel N k K r r = 1 := by
  simp only [tateDimensionKernel, dampedIntegerKernel_self, Finset.prod_const_one]

theorem tateDimensionKernel_edge {N n : ℕ} (hn : n ≠ 0)
    (k K : ℝ) {r s : ℚ} (hr : r ≠ 0) (he : s = n * r) :
    tateDimensionKernel N k K r s = tateDimensionMultiplier N k K n := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [dampedIntegerKernel_eq_tatePrimeRatio,
    padicValRat_edge_natAbs (Finset.mem_filter.mp hp).2 hn hr he]

private theorem tatePrimeParameter_bounds {p : ℕ} (hp : p.Prime)
    {k K : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K) :
    0 ≤ jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K) ∧
      jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K) ≤ 1 ∧
      0 ≤ (p : ℝ) ^ k / (p : ℝ) ^ K ∧ (p : ℝ) ^ k / (p : ℝ) ^ K ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hX := Real.one_le_rpow hp1.le hk
  have hXY := Real.rpow_le_rpow_of_exponent_le hp1.le hkK
  have hY := Real.one_lt_rpow hp1 hK
  have hh := jordanPrimeMixture_bounds hX hXY hY
  exact ⟨hh.1, hh.2, div_nonneg (zero_le_one.trans hX) (zero_lt_one.trans hY).le,
    (div_le_one (zero_lt_one.trans hY)).mpr hXY⟩

theorem tateDimensionKernel_posSemidef {ι : Type*} [Fintype ι]
    (N : ℕ) {k K : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K) (r : ι → ℚ) :
    Matrix.PosSemidef (fun i j => tateDimensionKernel N k K (r i) (r j)) := by
  apply finiteKernelProduct_posSemidef
  intro p hp
  obtain ⟨hρ0, hρ1, ht0, ht1⟩ :=
    tatePrimeParameter_bounds (Finset.mem_filter.mp hp).2 hk hkK hK
  exact dampedIntegerKernel_posSemidef hρ0 hρ1 ht0 ht1 (fun i => padicValRat p (r i))

/-- Positivity of every rational Tate graph is downward closed in dimension. -/
theorem RationalHeckePositive.tate_mono {A k K : ℝ} {N : ℕ}
    (hpos : RationalHeckePositive A N (fun n => jordanTotient K n / Real.sqrt n))
    (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K) :
    RationalHeckePositive A N (fun n => jordanTotient k n / Real.sqrt n) := by
  intro S hS hspread y
  let M : Matrix S S ℝ := fun r s => tateDimensionKernel N k K r s
  have hh := rationalHeckeForm_ge_of_psd_multiplier N
    (fun n => jordanTotient K n / Real.sqrt n) (tateDimensionMultiplier N k K) S M 0
    (tateDimensionKernel_posSemidef N hk hkK hK (fun r : S => (r : ℚ)))
    (fun r => by simp only [M, tateDimensionKernel_self, sub_zero])
    (fun n hn r s he => tateDimensionKernel_edge
      (by have := (Finset.mem_Icc.mp hn).1; omega) k K (hS r r.property).ne' he)
    (hpos S hS hspread) y
  simp only [zero_mul] at hh
  have he : rationalHeckeForm N
      (fun n => (jordanTotient K n / Real.sqrt n) * tateDimensionMultiplier N k K n) S y =
      rationalHeckeForm N (fun n => jordanTotient k n / Real.sqrt n) S y := by
    unfold rationalHeckeForm
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    dsimp only
    congr 1
    rw [div_mul_eq_mul_div,
      jordanTotient_mul_tateDimensionMultiplier hn0 (Finset.mem_Icc.mp hn).2 hK k]
  rwa [he] at hh

/-- Splitting off the identity coefficient writes the Tate form as a
normalized arithmetic correlation form, also for empty windows. -/
theorem tateFunction_eq_norm_add_correlations {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) +
      ∑ n ∈ Finset.Icc 2 (windowLevel A), jordanTotient k n / Real.sqrt n *
        ∫ u, H u * H (u + Real.log n) := by
  rcases Nat.eq_zero_or_pos (windowLevel A) with h0 | hpos
  · have hA : A < 0 := by
      by_contra h
      have hle := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp (not_lt.mp h))
      change 1 ≤ windowLevel A at hle
      omega
    have hz : ∀ u, H u = 0 := fun u => hH.vanish u fun hu => by
      linarith only [hu.1, hu.2, hA]
    rw [tateFunction_eq hH, h0]
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.Icc_eq_empty_of_lt (by omega : 0 < 2), Finset.sum_empty,
      hz, zero_pow two_ne_zero, integral_zero, add_zero]
  · have hI : Finset.Icc 1 (windowLevel A) = insert 1 (Finset.Icc 2 (windowLevel A)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [tateFunction_eq hH, hI, Finset.sum_insert (by simp), jordanTotient_one]
    simp only [Nat.cast_one, Real.sqrt_one, div_one, Real.log_one, add_zero, ← sq, one_mul]

/-- Tate positivity is equivalent to positivity of all finite rational
Hecke graphs that fit strictly inside the aperture. -/
theorem tateFunction_nonneg_iff_rationalHeckePositive (A k : ℝ) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      RationalHeckePositive A (windowLevel A) (fun n => jordanTotient k n / Real.sqrt n) := by
  have h := windowForm_nonneg_iff_rationalHeckePositive A (windowLevel A)
    (fun n => jordanTotient k n / Real.sqrt n)
  constructor
  · intro hp
    apply h.mp
    intro H hH
    rw [← tateFunction_eq_norm_add_correlations hH k]
    exact hp H hH
  · intro hp H hH
    rw [tateFunction_eq_norm_add_correlations hH k]
    exact h.mpr hp H hH

/-- At every aperture, a positive Tate dimension carries every lower
nonnegative dimension. No finite-component assumption is needed. -/
theorem tateFunction_nonneg_of_dimension_le {A k K : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K)
    (hpos : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H K) :
    ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k := by
  by_cases hK : K = 0
  · have hk0 : k = 0 := le_antisymm (hK ▸ hkK) hk
    subst k
    intro H hH
    rw [tateFunction_zero hH]
    exact integral_nonneg fun u => sq_nonneg (H u)
  · have hK0 : 0 < K := lt_of_le_of_ne (hk.trans hkK) (Ne.symm hK)
    exact (tateFunction_nonneg_iff_rationalHeckePositive A k).mpr
      (((tateFunction_nonneg_iff_rationalHeckePositive A K).mp hpos).tate_mono hk hkK hK0)

/-- Weight of the term that preserves every active prime valuation. -/
def tateDimensionMargin (N : ℕ) (k K : ℝ) : ℝ :=
  ∏ p ∈ tateActivePrimes N, (1 - jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K))

private def tateDimensionPinch (N : ℕ) (k K : ℝ) (r s : ℚ) : ℝ :=
  ∏ p ∈ tateActivePrimes N,
    (1 - jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K)) *
      if padicValRat p r = padicValRat p s then 1 else 0

private theorem tateDimensionPinch_self (N : ℕ) (k K : ℝ) (r : ℚ) :
    tateDimensionPinch N k K r r = tateDimensionMargin N k K := by
  simp only [tateDimensionPinch, tateDimensionMargin, if_true, mul_one]

private theorem tateDimensionPinch_edge {N n : ℕ} (hn : n ∈ Finset.Icc 2 N)
    (k K : ℝ) {r s : ℚ} (hr : r ≠ 0) (he : s = n * r) :
    tateDimensionPinch N k K r s = 0 := by
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by have := (Finset.mem_Icc.mp hn).1; omega : n ≠ 1)
  have hpP := primeFactors_subset_tateActivePrimes (Finset.mem_Icc.mp hn).2
    (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
  have hv : padicValNat p n ≠ 0 := by
    rw [← Nat.factorization_def n hp]
    exact (hp.factorization_pos_of_dvd hn0 hpn).ne'
  have hne : padicValRat p r ≠ padicValRat p s := by
    intro hh
    have habs := padicValRat_edge_natAbs hp hn0 hr he
    rw [hh, sub_self, Int.natAbs_zero] at habs
    exact hv habs.symm
  unfold tateDimensionPinch
  apply Finset.prod_eq_zero hpP
  rw [if_neg hne, mul_zero]

private theorem tateDimensionKernel_sub_pinch_posSemidef {ι : Type*} [Fintype ι]
    (N : ℕ) {k K : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K) (r : ι → ℚ) :
    Matrix.PosSemidef (fun i j => tateDimensionKernel N k K (r i) (r j) -
      tateDimensionPinch N k K (r i) (r j)) := by
  apply finiteKernelProduct_sub_posSemidef
    (U := fun (p : ℕ) i j => jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K) *
      ((p : ℝ) ^ k / (p : ℝ) ^ K) ^ (padicValRat p (r i) - padicValRat p (r j)).natAbs)
    (V := fun (p : ℕ) i j => (1 - jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K)) *
      if padicValRat p (r i) = padicValRat p (r j) then 1 else 0)
  · intro p hp
    obtain ⟨hρ0, _, ht0, ht1⟩ :=
      tatePrimeParameter_bounds (Finset.mem_filter.mp hp).2 hk hkK hK
    exact (integerDistanceKernel_posSemidef ht0 ht1 (fun i => padicValRat p (r i))).smul hρ0
  · intro p hp
    have hh := tatePrimeParameter_bounds (Finset.mem_filter.mp hp).2 hk hkK hK
    exact (integerEqualityKernel_posSemidef (fun i => padicValRat p (r i))).smul
      (sub_nonneg.mpr hh.2.1)

theorem tateDimensionMargin_pos (N : ℕ) {k K : ℝ} (hk : 0 ≤ k) (hkK : k < K) :
    0 < tateDimensionMargin N k K := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr (jordanPrimeMixture_lt_one
    (Real.one_le_rpow hp1.le hk) (Real.rpow_lt_rpow_of_exponent_lt hp1 hkK))

theorem tateDimensionMargin_le_one (N : ℕ) {k K : ℝ}
    (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K) : tateDimensionMargin N k K ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact sub_nonneg.mpr (tatePrimeParameter_bounds (Finset.mem_filter.mp hp).2 hk hkK hK).2.1
  · intro p hp
    have hh := (tatePrimeParameter_bounds (Finset.mem_filter.mp hp).2 hk hkK hK).1
    linarith only [hh]

/-- Lowering dimension retains an explicit diagonal share in every rational graph. -/
theorem rationalHeckeForm_ge_tateDimensionMargin {A k K : ℝ} {N : ℕ}
    (hk : 0 ≤ k) (hkK : k ≤ K) (hK : 0 < K)
    (hpos : RationalHeckePositive A N (fun n => jordanTotient K n / Real.sqrt n))
    (S : Finset ℚ) (hS : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) (y : ℚ → ℝ) :
    tateDimensionMargin N k K * (∑ r ∈ S, y r ^ 2) ≤
      rationalHeckeForm N (fun n => jordanTotient k n / Real.sqrt n) S y := by
  let M : Matrix S S ℝ := fun r s =>
    tateDimensionKernel N k K r s - tateDimensionPinch N k K r s
  have hh := rationalHeckeForm_ge_of_psd_multiplier N
    (fun n => jordanTotient K n / Real.sqrt n) (tateDimensionMultiplier N k K) S M
    (tateDimensionMargin N k K)
    (tateDimensionKernel_sub_pinch_posSemidef N hk hkK hK (fun r : S => (r : ℚ)))
    (fun r => by
      change tateDimensionKernel N k K r r - tateDimensionPinch N k K r r = _
      rw [tateDimensionKernel_self, tateDimensionPinch_self])
    (fun n hn r s he => by
      change tateDimensionKernel N k K r s - tateDimensionPinch N k K r s = _
      rw [tateDimensionKernel_edge
        (by have := (Finset.mem_Icc.mp hn).1; omega) k K (hS r r.property).ne' he,
        tateDimensionPinch_edge hn k K (hS r r.property).ne' he, sub_zero])
    (hpos S hS hspread) y
  convert hh using 1
  unfold rationalHeckeForm
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  congr 1
  rw [div_mul_eq_mul_div, jordanTotient_mul_tateDimensionMultiplier
    (by have := (Finset.mem_Icc.mp hn).1; omega) (Finset.mem_Icc.mp hn).2 hK k]

private theorem correlationForm_scale_identity {d : ℝ} (hd : d ≠ 0)
    (N : ℕ) (c f : ℕ → ℝ) (e : ℝ) :
    d * (e + ∑ n ∈ Finset.Icc 2 N, c n / d * f n) =
      d * e + ∑ n ∈ Finset.Icc 2 N, c n * f n := by
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  field_simp [hd]

/-- The rational graph/window equivalence preserves every margin below the
normalized diagonal. -/
theorem windowForm_ge_of_rationalHeckeForm_ge {A ε : ℝ} {N : ℕ} {c : ℕ → ℝ}
    (hε : ε < 1)
    (h : ∀ S : Finset ℚ, (∀ r ∈ S, 0 < r) →
      (∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) →
        ∀ y : ℚ → ℝ, ε * (∑ r ∈ S, y r ^ 2) ≤ rationalHeckeForm N c S y)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    ε * (∫ u, H u ^ 2) ≤ (∫ u, H u ^ 2) +
      ∑ n ∈ Finset.Icc 2 N, c n * ∫ u, H u * H (u + Real.log n) := by
  have hd : 0 < 1 - ε := sub_pos.mpr hε
  have hg : RationalHeckePositive A N (fun n => c n / (1 - ε)) := by
    intro S hS hspread y
    apply (mul_nonneg_iff_of_pos_left hd).mp
    change 0 ≤ (1 - ε) * ((∑ r ∈ S, y r ^ 2) +
      ∑ n ∈ Finset.Icc 2 N, c n / (1 - ε) *
        ∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then y r * y s else 0)
    rw [correlationForm_scale_identity hd.ne']
    have hh := h S hS hspread y
    unfold rationalHeckeForm at hh
    linarith only [hh]
  have hw := (windowForm_nonneg_iff_rationalHeckePositive A N
    (fun n => c n / (1 - ε))).mpr hg H hH
  have hh := mul_nonneg hd.le hw
  rw [correlationForm_scale_identity hd.ne'] at hh
  linarith only [hh]

private theorem tateDimensionMargin_lt_one {N : ℕ} (hN : 2 ≤ N) {k K : ℝ}
    (hk : 0 < k) (hkK : k ≤ K) : tateDimensionMargin N k K < 1 := by
  have hK : 0 < K := hk.trans_le hkK
  have h2 : 2 ∈ tateActivePrimes N := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, Nat.prime_two⟩
  have hρ0 : 0 < jordanPrimeMixture ((2 : ℝ) ^ k) ((2 : ℝ) ^ K) := by
    have hk2 := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hk
    have hK2 := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hK
    exact div_pos (mul_pos (sub_pos.mpr hk2) (zero_lt_one.trans hK2))
      (mul_pos (sub_pos.mpr hK2) (zero_lt_one.trans hk2))
  have hf0 : 0 ≤ 1 - jordanPrimeMixture ((2 : ℝ) ^ k) ((2 : ℝ) ^ K) :=
    sub_nonneg.mpr (tatePrimeParameter_bounds Nat.prime_two hk.le hkK hK).2.1
  have hrest : (∏ p ∈ (tateActivePrimes N).erase 2,
      (1 - jordanPrimeMixture ((p : ℝ) ^ k) ((p : ℝ) ^ K))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact sub_nonneg.mpr (tatePrimeParameter_bounds
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2 hk.le hkK hK).2.1
    · intro p hp
      have hh := (tatePrimeParameter_bounds
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2 hk.le hkK hK).1
      linarith only [hh]
  unfold tateDimensionMargin
  rw [← Finset.mul_prod_erase _ _ h2]
  norm_num only [Nat.cast_ofNat]
  have hh := mul_le_mul_of_nonneg_left hrest hf0
  linarith only [hh, hρ0]

/-- Lowering a positive Tate dimension leaves a uniform positive margin.
The explicit coefficient is the product of the valuation-preserving shares. -/
theorem tateFunction_ge_dimensionMargin {A k K : ℝ} (hk : 0 ≤ k) (hkK : k < K)
    (hpos : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H K)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    tateDimensionMargin (windowLevel A) k K * (∫ u, H u ^ 2) ≤ tateFunction A H k := by
  rcases eq_or_lt_of_le hk with rfl | hk0
  · rw [tateFunction_zero hH]
    simp only [tateDimensionMargin, jordanPrimeMixture, Real.rpow_zero, sub_self,
      zero_mul, zero_div, sub_zero, Finset.prod_const_one, one_mul, le_refl]
  · by_cases hN : 2 ≤ windowLevel A
    · rw [tateFunction_eq_norm_add_correlations hH k]
      apply windowForm_ge_of_rationalHeckeForm_ge
        (tateDimensionMargin_lt_one hN hk0 hkK.le)
      · exact rationalHeckeForm_ge_tateDimensionMargin hk0.le hkK.le (hk0.trans hkK)
          ((tateFunction_nonneg_iff_rationalHeckePositive A K).mp hpos)
      · exact hH
    · have hlt : windowLevel A < 2 := Nat.lt_of_not_ge hN
      rw [tateFunction_eq_norm_add_correlations hH k]
      simp only [tateDimensionMargin, tateActivePrimes, Finset.Icc_eq_empty_of_lt hlt,
        Finset.filter_empty, Finset.prod_empty, Finset.sum_empty, one_mul, add_zero, le_refl]

/-- Every dimension strictly below a positive Tate dimension has a positive
uniform quadratic-form floor on the same window. -/
theorem exists_tateFunction_uniform_floor_of_dimension_lt {A k K : ℝ}
    (hk : 0 ≤ k) (hkK : k < K)
    (hpos : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℝ → ℝ, IsWindowTest A H →
      ε * (∫ u, H u ^ 2) ≤ tateFunction A H k :=
  ⟨tateDimensionMargin (windowLevel A) k K, tateDimensionMargin_pos _ hk hkK,
    fun _ hH => tateFunction_ge_dimensionMargin hk hkK hpos hH⟩

#print axioms rationalHeckeForm_ge_of_gram_multiplier
#print axioms integerDistanceKernel_posSemidef
#print axioms rationalHeckeForm_ge_of_psd_multiplier
#print axioms tateFunction_nonneg_of_dimension_le
#print axioms exists_tateFunction_uniform_floor_of_dimension_lt

end GaloisForLFunctions.WindowTowerOfSpecZ
