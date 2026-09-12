import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue
import GaloisForLFunctions.HTGeometry.PaleyZygmund

/-!
# A subpower fourth-moment bound for complex Steinhaus carriers

Squaring a complex-coefficient Steinhaus carrier turns its coefficients into the finite
Dirichlet convolution. Complex Parseval then identifies the fourth moment with the convolution
`ell^2` energy. Product fibres inject into divisor sets, so the unconditional divisor bound gives
an arbitrarily small power loss.
-/

noncomputable section

namespace RHTower

open MeasureTheory
open SteinhausModel

/-- A complex Steinhaus carrier indexed by the positive integers `1, ..., M`. -/
noncomputable def steinhausFinCarrier (M : ℕ) (a : Fin M → ℂ) (omega : Omega) : ℂ :=
  ∑ j : Fin M, a j * X ((j : ℕ) + 1) omega

/-- Reindex a finite successor carrier from `Fin M` to the positive interval `[1, M]`. -/
theorem sum_fin_succ_eq_sum_Icc {A : Type*} [AddCommMonoid A]
    (M : ℕ) (g : ℕ → A) :
    ∑ j : Fin M, g ((j : ℕ) + 1) = ∑ n ∈ Finset.Icc 1 M, g n := by
  classical
  rw [← Sieve.image_succ_univ M, Finset.sum_image (Sieve.succ_injOn M)]

theorem norm_steinhausFinCarrier_le (M : ℕ) (a : Fin M → ℂ) (omega : Omega) :
    ‖steinhausFinCarrier M a omega‖ ≤ ∑ j : Fin M, ‖a j‖ := by
  unfold steinhausFinCarrier
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [norm_mul, norm_X, mul_one]

theorem measurable_steinhausFinCarrier (M : ℕ) (a : Fin M → ℂ) :
    Measurable (steinhausFinCarrier M a) := by
  unfold steinhausFinCarrier
  exact Finset.measurable_sum Finset.univ fun j _ => (measurable_X ((j : ℕ) + 1)).const_mul _

theorem integrable_norm_pow_steinhausFinCarrier (M : ℕ) (a : Fin M → ℂ) (k : ℕ) :
    Integrable (fun omega => ‖steinhausFinCarrier M a omega‖ ^ k) steinhausMeasure := by
  set B : ℝ := ∑ j : Fin M, ‖a j‖
  apply Integrable.mono' (integrable_const (B ^ k))
  · exact ((measurable_steinhausFinCarrier M a).norm.pow_const k).aestronglyMeasurable
  · filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausFinCarrier_le M a omega) k

theorem steinhausFinCarrier_eq_zero_of_variance_eq_zero
    (M : ℕ) (a : Fin M → ℂ)
    (hvar : (∑ j : Fin M, ‖a j‖ ^ 2) = 0) :
    steinhausFinCarrier M a = 0 := by
  have ha : ∀ j : Fin M, a j = 0 := by
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin M))) => sq_nonneg ‖a k‖)).mp hvar
      j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  funext omega
  unfold steinhausFinCarrier
  simp [ha]

/-- Complex Parseval for a carrier indexed by `Fin M`. -/
theorem integral_normSq_steinhausFinCarrier (M : ℕ) (a : Fin M → ℂ) :
    ∫ omega, ‖steinhausFinCarrier M a omega‖ ^ 2 ∂steinhausMeasure =
      ∑ j : Fin M, ‖a j‖ ^ 2 := by
  classical
  have hcomplex :
      ∫ omega, steinhausFinCarrier M a omega *
          (starRingEnd ℂ) (steinhausFinCarrier M a omega) ∂steinhausMeasure =
        ((∑ j : Fin M, ‖a j‖ ^ 2 : ℝ) : ℂ) := by
    have hexp : ∀ omega : Omega,
        steinhausFinCarrier M a omega *
            (starRingEnd ℂ) (steinhausFinCarrier M a omega) =
          ∑ j : Fin M, ∑ k : Fin M,
            (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega)) := by
      intro omega
      unfold steinhausFinCarrier
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
    have hinner : ∀ j : Fin M,
        ∫ omega, ∑ k : Fin M,
            (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
              ∂steinhausMeasure =
          a j * (starRingEnd ℂ) (a j) := by
      intro j
      have hterm : ∀ k : Fin M,
          ∫ omega, (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
              ∂steinhausMeasure =
            if j = k then a j * (starRingEnd ℂ) (a k) else 0 := by
        intro k
        rw [integral_const_mul, integral_X_mul_conj (by omega) (by omega)]
        rcases eq_or_ne j k with rfl | hjk
        · rw [if_pos rfl, if_pos rfl, mul_one]
        · have hnat : (j : ℕ) + 1 ≠ (k : ℕ) + 1 := by
            intro h
            apply hjk
            exact Fin.ext (by omega)
          rw [if_neg hnat, if_neg hjk, mul_zero]
      calc
        (∫ omega, ∑ k : Fin M,
            (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
              ∂steinhausMeasure) =
            ∑ k : Fin M, ∫ omega, (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
              ∂steinhausMeasure := by
                exact integral_finsetSum (μ := steinhausMeasure)
                  (Finset.univ : Finset (Fin M))
                  (f := fun k omega => (a j * (starRingEnd ℂ) (a k)) *
                    (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega)))
                  (fun k _ =>
                    (integrable_X_mul_conj ((j : ℕ) + 1) ((k : ℕ) + 1)).const_mul _)
        _ = ∑ k : Fin M, if j = k then a j * (starRingEnd ℂ) (a k) else 0 := by
          exact Finset.sum_congr rfl (fun k _ => hterm k)
        _ = a j * (starRingEnd ℂ) (a j) := by simp
    calc
      (∫ omega, ∑ j : Fin M, ∑ k : Fin M,
          (a j * (starRingEnd ℂ) (a k)) *
            (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
            ∂steinhausMeasure) =
          ∑ j : Fin M, ∫ omega, ∑ k : Fin M,
            (a j * (starRingEnd ℂ) (a k)) *
              (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega))
              ∂steinhausMeasure := by
                exact integral_finsetSum (μ := steinhausMeasure)
                  (Finset.univ : Finset (Fin M))
                  (f := fun j omega => ∑ k : Fin M,
                    (a j * (starRingEnd ℂ) (a k)) *
                      (X ((j : ℕ) + 1) omega * (starRingEnd ℂ) (X ((k : ℕ) + 1) omega)))
                  (fun j _ => integrable_finsetSum (Finset.univ : Finset (Fin M))
                    (fun k _ =>
                      (integrable_X_mul_conj ((j : ℕ) + 1) ((k : ℕ) + 1)).const_mul _))
      _ = ∑ j : Fin M, a j * (starRingEnd ℂ) (a j) :=
        Finset.sum_congr rfl (fun j _ => hinner j)
      _ = ((∑ j : Fin M, ‖a j‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Complex.mul_conj']
  have hpoint : ∀ omega : Omega,
      steinhausFinCarrier M a omega * (starRingEnd ℂ) (steinhausFinCarrier M a omega) =
        ((‖steinhausFinCarrier M a omega‖ ^ 2 : ℝ) : ℂ) := by
    intro omega
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_complex_ofReal] at hcomplex
  exact_mod_cast hcomplex

/-- Squaring a complex Steinhaus carrier produces the finite Dirichlet convolution carrier. -/
theorem steinhausFinCarrier_sq_eq_dirConv (M : ℕ) (a : Fin M → ℂ) (omega : Omega) :
    steinhausFinCarrier M a omega ^ 2 =
      steinhausFinCarrier (M * M) (Sieve.dirConv M M a a) omega := by
  classical
  unfold steinhausFinCarrier
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.univ_product_univ]
  have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin M × Fin M)),
      Sieve.prodIdx q ∈ (Finset.univ : Finset (Fin (M * M))) :=
    fun q _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : Fin M × Fin M =>
      (a q.1 * X ((q.1 : ℕ) + 1) omega) * (a q.2 * X ((q.2 : ℕ) + 1) omega))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Sieve.dirConv, Sieve.filter_prodIdx_eq r, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  have hprod : (r : ℕ) + 1 = ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := by
    rw [← hq, Sieve.prodIdx_val]
  rw [hprod, X_mul (by omega) (by omega)]
  ring

/-- Exact fourth moment: the squared carrier has the convolution coefficient energy. -/
theorem integral_norm_four_steinhausFinCarrier_eq (M : ℕ) (a : Fin M → ℂ) :
    ∫ omega, ‖steinhausFinCarrier M a omega‖ ^ 4 ∂steinhausMeasure =
      ∑ r : Fin (M * M), ‖Sieve.dirConv M M a a r‖ ^ 2 := by
  have hpoint : ∀ omega : Omega,
      ‖steinhausFinCarrier M a omega‖ ^ 4 =
        ‖steinhausFinCarrier (M * M) (Sieve.dirConv M M a a) omega‖ ^ 2 := by
    intro omega
    calc
      ‖steinhausFinCarrier M a omega‖ ^ 4 =
          ‖steinhausFinCarrier M a omega ^ 2‖ ^ 2 := by rw [norm_pow]; ring
      _ = ‖steinhausFinCarrier (M * M) (Sieve.dirConv M M a a) omega‖ ^ 2 := by
        rw [steinhausFinCarrier_sq_eq_dirConv]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact integral_normSq_steinhausFinCarrier (M * M) (Sieve.dirConv M M a a)

/-- **Subpower fourth-moment bound for arbitrary complex Steinhaus coefficients.** -/
theorem exists_integral_norm_four_steinhausFinCarrier_le_rpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (a : Fin M → ℂ),
      (∫ omega, ‖steinhausFinCarrier M a omega‖ ^ 4 ∂steinhausMeasure) ≤
        C * ((M * M : ℕ) : ℝ) ^ epsilon * (∑ j : Fin M, ‖a j‖ ^ 2) ^ 2 := by
  obtain ⟨C, hC, hconv⟩ := Sieve.exists_sum_norm_sq_dirConv_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro M a
  rw [integral_norm_four_steinhausFinCarrier_eq]
  calc
    ∑ r : Fin (M * M), ‖Sieve.dirConv M M a a r‖ ^ 2 ≤
        C * ((M * M : ℕ) : ℝ) ^ epsilon *
          ((∑ j : Fin M, ‖a j‖ ^ 2) * (∑ j : Fin M, ‖a j‖ ^ 2)) :=
      hconv M M a a
    _ = C * ((M * M : ℕ) : ℝ) ^ epsilon * (∑ j : Fin M, ‖a j‖ ^ 2) ^ 2 := by
      ring

/-- Sum of squared conditional-channel magnitudes. -/
noncomputable def steinhausFinEnergy {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) (omega : Omega) : ℝ :=
  ∑ i ∈ P, ‖steinhausFinCarrier M (a i) omega‖ ^ 2

/-- Sum of the coefficient variances of a finite channel family. -/
noncomputable def steinhausFinTotalVariance {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) : ℝ :=
  ∑ i ∈ P, ∑ j : Fin M, ‖a i j‖ ^ 2

theorem measurable_steinhausFinEnergy {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) :
    Measurable (steinhausFinEnergy P M a) := by
  unfold steinhausFinEnergy
  exact Finset.measurable_sum P fun i _ =>
    ((measurable_steinhausFinCarrier M (a i)).norm).pow_const 2

theorem steinhausFinEnergy_nonneg {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) (omega : Omega) :
    0 ≤ steinhausFinEnergy P M a omega := by
  unfold steinhausFinEnergy
  positivity

theorem steinhausFinEnergy_le {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) (omega : Omega) :
    steinhausFinEnergy P M a omega ≤
      ∑ i ∈ P, (∑ j : Fin M, ‖a i j‖) ^ 2 := by
  unfold steinhausFinEnergy
  refine Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_steinhausFinCarrier_le M (a i) omega) 2

theorem integrable_steinhausFinEnergy_pow {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) (k : ℕ) :
    Integrable (fun omega => steinhausFinEnergy P M a omega ^ k) steinhausMeasure := by
  set B : ℝ := ∑ i ∈ P, (∑ j : Fin M, ‖a i j‖) ^ 2
  apply Integrable.mono' (integrable_const (B ^ k))
  · exact ((measurable_steinhausFinEnergy P M a).pow_const k).aestronglyMeasurable
  · filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (steinhausFinEnergy_nonneg P M a omega) k)]
    exact pow_le_pow_left₀ (steinhausFinEnergy_nonneg P M a omega)
      (steinhausFinEnergy_le P M a omega) k

/-- Exact mean of the total conditional-channel energy. -/
theorem integral_steinhausFinEnergy_eq_totalVariance {ι : Type*} (P : Finset ι) (M : ℕ)
    (a : ι → Fin M → ℂ) :
    ∫ omega, steinhausFinEnergy P M a omega ∂steinhausMeasure =
      steinhausFinTotalVariance P M a := by
  unfold steinhausFinEnergy steinhausFinTotalVariance
  rw [integral_finsetSum P (fun i _ => integrable_norm_pow_steinhausFinCarrier M (a i) 2)]
  exact Finset.sum_congr rfl fun i _ => integral_normSq_steinhausFinCarrier M (a i)

/-- A uniform fourth-moment bound for each positive-variance channel controls the second moment of
their total conditional energy with no loss in the number of channels. -/
theorem integral_steinhausFinEnergy_sq_le_of_fourth
    {ι : Type*} (P : Finset ι) (M : ℕ) (a : ι → Fin M → ℂ)
    {K : ℝ}
    (hvar : ∀ i ∈ P, 0 < ∑ j : Fin M, ‖a i j‖ ^ 2)
    (hfourth : ∀ i ∈ P,
      (∫ omega, ‖steinhausFinCarrier M (a i) omega‖ ^ 4 ∂steinhausMeasure) ≤
        K * (∑ j : Fin M, ‖a i j‖ ^ 2) ^ 2) :
    (∫ omega, steinhausFinEnergy P M a omega ^ 2 ∂steinhausMeasure) ≤
      K * steinhausFinTotalVariance P M a ^ 2 := by
  classical
  by_cases hP : P.Nonempty
  · set v : ι → ℝ := fun i => ∑ j : Fin M, ‖a i j‖ ^ 2 with hv
    set V : ℝ := ∑ i ∈ P, v i with hV
    obtain ⟨i0, hi0⟩ := hP
    have hVpos : 0 < V := Finset.sum_pos' (fun i hi => by simpa [v] using (hvar i hi).le)
      ⟨i0, hi0, by simpa [v] using hvar i0 hi0⟩
    have hpoint : ∀ omega : Omega,
        steinhausFinEnergy P M a omega ^ 2 ≤
          V * ∑ i ∈ P, (‖steinhausFinCarrier M (a i) omega‖ ^ 2) ^ 2 / v i := by
      intro omega
      have hsed := Finset.sq_sum_div_le_sum_sq_div P
        (fun i => ‖steinhausFinCarrier M (a i) omega‖ ^ 2)
        (g := v) (fun i hi => by simpa [v] using hvar i hi)
      have hmul := (div_le_iff₀ hVpos).mp (by simpa [steinhausFinEnergy, V] using hsed)
      simpa [steinhausFinEnergy, mul_comm] using hmul
    have hpow4 : ∀ i : ι, Integrable
        (fun omega => (‖steinhausFinCarrier M (a i) omega‖ ^ 2) ^ 2)
        steinhausMeasure := by
      intro i
      simpa only [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul] using
        integrable_norm_pow_steinhausFinCarrier M (a i) 4
    have hrightInt : Integrable (fun omega =>
        V * ∑ i ∈ P, (‖steinhausFinCarrier M (a i) omega‖ ^ 2) ^ 2 / v i)
        steinhausMeasure := by
      apply Integrable.const_mul
      exact integrable_finsetSum P fun i hi =>
        (hpow4 i).div_const (v i)
    have hmono :
        (∫ omega, steinhausFinEnergy P M a omega ^ 2 ∂steinhausMeasure) ≤
          ∫ omega, V * ∑ i ∈ P,
            (‖steinhausFinCarrier M (a i) omega‖ ^ 2) ^ 2 / v i
            ∂steinhausMeasure := by
      exact integral_mono (integrable_steinhausFinEnergy_pow P M a 2) hrightInt hpoint
    calc
      (∫ omega, steinhausFinEnergy P M a omega ^ 2 ∂steinhausMeasure) ≤
          ∫ omega, V * ∑ i ∈ P,
            (‖steinhausFinCarrier M (a i) omega‖ ^ 2) ^ 2 / v i
            ∂steinhausMeasure := hmono
      _ = V * ∑ i ∈ P,
          (∫ omega, ‖steinhausFinCarrier M (a i) omega‖ ^ 4 ∂steinhausMeasure) / v i := by
        rw [integral_const_mul, integral_finsetSum P]
        · congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [integral_div]
          congr 1
          ring_nf
        · intro i hi
          exact (hpow4 i).div_const (v i)
      _ ≤ V * ∑ i ∈ P, (K * v i ^ 2) / v i := by
        apply mul_le_mul_of_nonneg_left _ hVpos.le
        refine Finset.sum_le_sum fun i hi => ?_
        exact div_le_div_of_nonneg_right (by simpa [v] using hfourth i hi) (hvar i hi).le
      _ = K * steinhausFinTotalVariance P M a ^ 2 := by
        have hvne : ∀ i ∈ P, v i ≠ 0 := fun i hi => (by simpa [v] using (hvar i hi).ne')
        rw [show (∑ i ∈ P, (K * v i ^ 2) / v i) = K * V by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          field_simp [hvne i hi]
        ]
        simp only [V, v, steinhausFinTotalVariance]
        ring
  · have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp [steinhausFinEnergy, steinhausFinTotalVariance]

/-- **Subpower second-moment bound for total conditional channel energy.** -/
theorem exists_integral_steinhausFinEnergy_sq_le_rpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (P : Finset ι) (M : ℕ)
      (a : ι → Fin M → ℂ),
      (∀ i ∈ P, 0 < ∑ j : Fin M, ‖a i j‖ ^ 2) →
      (∫ omega, steinhausFinEnergy P M a omega ^ 2 ∂steinhausMeasure) ≤
        (C * ((M * M : ℕ) : ℝ) ^ epsilon) * steinhausFinTotalVariance P M a ^ 2 := by
  obtain ⟨C, hC, hsingle⟩ :=
    exists_integral_norm_four_steinhausFinCarrier_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι P M a hvar
  exact integral_steinhausFinEnergy_sq_le_of_fourth P M a hvar
    (fun i hi => hsingle M (a i))

/-- Paley--Zygmund converts a total-energy second-moment bound into a quantitative positive-mass
event, with no channel-count loss. -/
theorem measure_steinhausFinEnergy_gt_half_ge_of_second_moment
    {ι : Type*} (P : Finset ι) (M : ℕ) (a : ι → Fin M → ℂ)
    (hP : P.Nonempty)
    (hvar : ∀ i ∈ P, 0 < ∑ j : Fin M, ‖a i j‖ ^ 2)
    {K : ℝ} (hK : 0 < K)
    (hsecond :
      (∫ omega, steinhausFinEnergy P M a omega ^ 2 ∂steinhausMeasure) ≤
        K * steinhausFinTotalVariance P M a ^ 2) :
    1 / (4 * K) ≤
      (steinhausMeasure {omega |
        (1 / 2 : ℝ) * steinhausFinTotalVariance P M a <
          steinhausFinEnergy P M a omega}).toReal := by
  have hmeanpos : 0 < steinhausFinTotalVariance P M a := by
    obtain ⟨i0, hi0⟩ := hP
    unfold steinhausFinTotalVariance
    exact Finset.sum_pos' (fun i hi => (hvar i hi).le) ⟨i0, hi0, hvar i0 hi0⟩
  have hEi : Integrable (steinhausFinEnergy P M a) steinhausMeasure := by
    simpa using integrable_steinhausFinEnergy_pow P M a 1
  have hpz := GaloisForLFunctions.HTGeometry.paley_zygmund
    (μ := steinhausMeasure) (Z := steinhausFinEnergy P M a)
    (measurable_steinhausFinEnergy P M a)
    (steinhausFinEnergy_nonneg P M a) hEi
    (integrable_steinhausFinEnergy_pow P M a 2)
    (θ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [integral_steinhausFinEnergy_eq_totalVariance] at hpz
  set q : ℝ :=
    (steinhausMeasure {omega |
      (1 / 2 : ℝ) * steinhausFinTotalVariance P M a <
        steinhausFinEnergy P M a omega}).toReal
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hstep :
      (1 - (1 / 2 : ℝ)) ^ 2 * steinhausFinTotalVariance P M a ^ 2 ≤
        (K * steinhausFinTotalVariance P M a ^ 2) * q := by
    refine hpz.trans ?_
    exact mul_le_mul_of_nonneg_right hsecond hq0
  have hvarSq : 0 < steinhausFinTotalVariance P M a ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Subpower positive-mass event for total complex conditional-channel energy.** -/
theorem exists_measure_steinhausFinEnergy_gt_half_ge_rpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (P : Finset ι) (M : ℕ)
      (a : ι → Fin M → ℂ),
      P.Nonempty →
      (∀ i ∈ P, 0 < ∑ j : Fin M, ‖a i j‖ ^ 2) →
      1 / (4 * (C * ((M * M : ℕ) : ℝ) ^ epsilon)) ≤
        (steinhausMeasure {omega |
          (1 / 2 : ℝ) * steinhausFinTotalVariance P M a <
            steinhausFinEnergy P M a omega}).toReal := by
  obtain ⟨C, hC, hsecond⟩ := exists_integral_steinhausFinEnergy_sq_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι P M a hP hvar
  have hM : M ≠ 0 := by
    intro hMz
    subst M
    obtain ⟨i0, hi0⟩ := hP
    have := hvar i0 hi0
    simp at this
  have hMMpos : (0 : ℝ) < ((M * M : ℕ) : ℝ) := by positivity
  exact measure_steinhausFinEnergy_gt_half_ge_of_second_moment P M a hP hvar
    (mul_pos hC (Real.rpow_pos_of_pos hMMpos epsilon)) (hsecond P M a hvar)

/-- Zero-variance channels can be discarded exactly, so aggregate positive variance alone is
enough for the same subpower Paley--Zygmund event. -/
theorem exists_measure_steinhausFinEnergy_gt_half_ge_rpow_of_totalVariance_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (P : Finset ι) (M : ℕ)
      (a : ι → Fin M → ℂ),
      0 < steinhausFinTotalVariance P M a →
      1 / (4 * (C * ((M * M : ℕ) : ℝ) ^ epsilon)) ≤
        (steinhausMeasure {omega |
          (1 / 2 : ℝ) * steinhausFinTotalVariance P M a <
            steinhausFinEnergy P M a omega}).toReal := by
  obtain ⟨C, hC, hbase⟩ := exists_measure_steinhausFinEnergy_gt_half_ge_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro ι P M a htotal
  classical
  let Q : Finset ι := P.filter fun i => 0 < ∑ j : Fin M, ‖a i j‖ ^ 2
  have hnonneg : ∀ i : ι, 0 ≤ ∑ j : Fin M, ‖a i j‖ ^ 2 := fun i => by positivity
  have hVeq : steinhausFinTotalVariance Q M a = steinhausFinTotalVariance P M a := by
    unfold steinhausFinTotalVariance
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiP hiQ
    have hnot : ¬ 0 < ∑ j : Fin M, ‖a i j‖ ^ 2 := by
      simpa [Q, hiP] using hiQ
    exact le_antisymm (not_lt.mp hnot) (hnonneg i)
  have hEeq : steinhausFinEnergy Q M a = steinhausFinEnergy P M a := by
    funext omega
    unfold steinhausFinEnergy
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiP hiQ
    have hnot : ¬ 0 < ∑ j : Fin M, ‖a i j‖ ^ 2 := by
      simpa [Q, hiP] using hiQ
    have hvzero : (∑ j : Fin M, ‖a i j‖ ^ 2) = 0 :=
      le_antisymm (not_lt.mp hnot) (hnonneg i)
    rw [show steinhausFinCarrier M (a i) omega = 0 by
      have hz := steinhausFinCarrier_eq_zero_of_variance_eq_zero M (a i) hvzero
      exact congrFun hz omega]
    norm_num
  have hQ : Q.Nonempty := by
    by_contra hQempty
    have : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQempty
    have hzero : steinhausFinTotalVariance P M a = 0 := by
      rw [← hVeq, this]
      simp [steinhausFinTotalVariance]
    linarith
  have hQvar : ∀ i ∈ Q, 0 < ∑ j : Fin M, ‖a i j‖ ^ 2 := by
    intro i hi
    change i ∈ P.filter (fun i => 0 < ∑ j : Fin M, ‖a i j‖ ^ 2) at hi
    exact (Finset.mem_filter.mp hi).2
  have h := hbase Q M a hQ hQvar
  simpa only [hVeq, hEeq] using h

end RHTower

end
