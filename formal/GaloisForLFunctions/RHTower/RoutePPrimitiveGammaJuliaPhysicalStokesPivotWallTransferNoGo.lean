import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallRealZeroClosure
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtMovingPair
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantScaling
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.CoherentSourceFunctor

/-!
# Physical P-G105 pivot-wall transfer and Xi limit obstruction

The physical Hellinger Stokes channel has a varying signed-permutation pivot.  This file proves
that, under its natural current normalization, that pivot is Hilbert--Schmidt-null relative to the
balanced channel along the canonical aperture sequence.  The full ordinary determinant therefore
has the exact aperture wall as its locally uniform limit.  The established quadratic wall/Xi
mismatch then rules out a normalized-Xi limit for the actual physical channel, not merely for its
balanced specialization.
-/

namespace RHTower

open Filter Topology
open scoped BigOperators
open HilbertSchmidt

theorem routePPrimitiveGammaJuliaStokesCofinalChild_hsNorm_le_firstTrace
    {d : ℝ} (hd : 0 < d) :
    hsNorm (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) ≤
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  let w : Nat.Primes → ℝ :=
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d
  let K := routePPrimitiveGammaJuliaStokesCofinalChildKernel d
  let W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  have hw : Summable w := by
    exact summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hprod : Summable (fun pq : Nat.Primes × Nat.Primes => w pq.1 * w pq.2) := by
    exact summable_mul_of_summable_norm hw.norm hw.norm
  have hK : IsHS K := by
    exact routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hentry : ∀ pq : Nat.Primes × Nat.Primes, ‖K pq‖ ^ 2 ≤ w pq.1 * w pq.2 := by
    intro pq
    exact norm_sq_routePPrimitiveGammaJuliaStokesCofinalChildKernel_le hd pq
  have hsq : hsNormSq K ≤ W ^ 2 := by
    calc
      hsNormSq K = ∑' pq, ‖K pq‖ ^ 2 := rfl
      _ ≤ ∑' pq : Nat.Primes × Nat.Primes, w pq.1 * w pq.2 :=
        Summable.tsum_mono hK hprod hentry
      _ = (∑' p, w p) * ∑' q, w q := by
        exact (hw.tsum_mul_tsum hw hprod).symm
      _ = W ^ 2 := by
        rw [tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
        simp [W, pow_two]
  have hW0 : 0 ≤ W := by
    exact (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).le
  rw [hsNorm]
  exact (Real.sqrt_le_iff).mpr ⟨hW0, hsq⟩

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNormSq_delta_factor
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    hsNormSq
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1) =
      (∑ ij : Fin 2 × Fin 2,
        ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2 -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2) *
        hsNormSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) := by
  let A := routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r
  let B := routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1
  let K := routePPrimitiveGammaJuliaStokesCofinalChildKernel d
  let a : Fin 2 × Fin 2 → ℝ := fun ij => ‖A ij.1 ij.2 - B ij.1 ij.2‖ ^ 2
  let b : Nat.Primes × Nat.Primes → ℝ := fun pq => ‖K pq‖ ^ 2
  have ha : Summable a := Summable.of_finite
  have hK : IsHS K := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hb : Summable b := hK
  have hab : Summable (fun uv : (Fin 2 × Fin 2) × (Nat.Primes × Nat.Primes) =>
      a uv.1 * b uv.2) := by
    exact summable_mul_of_summable_norm ha.norm hb.norm
  calc
    hsNormSq
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1) =
        ∑' xy,
          ‖(routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r -
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1) xy‖ ^ 2 := rfl
    _ = ∑' uv : (Fin 2 × Fin 2) × (Nat.Primes × Nat.Primes), a uv.1 * b uv.2 := by
      rw [← routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv.tsum_eq]
      apply tsum_congr
      rintro ⟨⟨i, p⟩, ⟨j, q⟩⟩
      simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv,
        A, B, K, a, b, Pi.sub_apply,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel]
      rw [← sub_mul, norm_mul, mul_pow]
      change _ = ‖A i j - B i j‖ ^ 2 * ‖K (p, q)‖ ^ 2
      rfl
    _ = (∑' ij, a ij) * ∑' pq, b pq :=
      (ha.tsum_mul_tsum hb hab).symm
    _ = _ := by
      simp only [tsum_fintype, a, b, A, B, K, hsNormSq]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNormSq_factor
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    hsNormSq (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) =
      (∑ ij : Fin 2 × Fin 2,
        ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2‖ ^ 2) *
        hsNormSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) := by
  let A := routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r
  let K := routePPrimitiveGammaJuliaStokesCofinalChildKernel d
  let a : Fin 2 × Fin 2 → ℝ := fun ij => ‖A ij.1 ij.2‖ ^ 2
  let b : Nat.Primes × Nat.Primes → ℝ := fun pq => ‖K pq‖ ^ 2
  have ha : Summable a := Summable.of_finite
  have hK : IsHS K := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hb : Summable b := hK
  have hab : Summable (fun uv : (Fin 2 × Fin 2) × (Nat.Primes × Nat.Primes) =>
      a uv.1 * b uv.2) := by
    exact summable_mul_of_summable_norm ha.norm hb.norm
  calc
    hsNormSq (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) =
        ∑' xy, ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r xy‖ ^ 2 := rfl
    _ = ∑' uv : (Fin 2 × Fin 2) × (Nat.Primes × Nat.Primes), a uv.1 * b uv.2 := by
      rw [← routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv.tsum_eq]
      apply tsum_congr
      rintro ⟨⟨i, p⟩, ⟨j, q⟩⟩
      simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv, A, K, a, b,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel]
      rw [norm_mul, mul_pow]
      change _ = ‖A i j‖ ^ 2 * ‖K (p, q)‖ ^ 2
      rfl
    _ = (∑' ij, a ij) * ∑' pq, b pq :=
      (ha.tsum_mul_tsum hb hab).symm
    _ = _ := by
      simp only [tsum_fintype, a, b, A, K, hsNormSq]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNorm_le_channel_energy_mul_firstTrace
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    hsNorm (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) ≤
      Real.sqrt (∑ ij : Fin 2 × Fin 2,
        ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2‖ ^ 2) *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  let E : ℝ := ∑ ij : Fin 2 × Fin 2,
    ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2‖ ^ 2
  let W : ℝ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  have hE : 0 ≤ E := Finset.sum_nonneg fun ij _ => sq_nonneg _
  have hW : 0 ≤ W := (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).le
  have hchild : hsNormSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) ≤ W ^ 2 := by
    have h := routePPrimitiveGammaJuliaStokesCofinalChild_hsNorm_le_firstTrace hd
    have hnonneg := hsNorm_nonneg (routePPrimitiveGammaJuliaStokesCofinalChildKernel d)
    have hsq := pow_le_pow_left₀ hnonneg h 2
    simpa only [W, hsNorm, Real.sq_sqrt
      (hsNormSq_nonneg (routePPrimitiveGammaJuliaStokesCofinalChildKernel d))] using hsq
  calc
    hsNorm (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) =
        Real.sqrt (E * hsNormSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d)) := by
      rw [hsNorm, routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNormSq_factor hd r]
    _ ≤ Real.sqrt (E * W ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hchild hE
    _ = Real.sqrt E * W := by
      rw [Real.sqrt_mul hE, Real.sqrt_sq_eq_abs, abs_of_nonneg hW]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNorm_delta_le
    {d : ℝ} (hd : 0 < d) (r : ℝ) :
    hsNorm
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1) ≤
      Real.sqrt
        ((∑ ij : Fin 2 × Fin 2,
          ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2 -
            routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2) *
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2) := by
  let a : ℝ := ∑ ij : Fin 2 × Fin 2,
    ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2 -
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2
  have ha : 0 ≤ a := by
    exact Finset.sum_nonneg fun ij _ => sq_nonneg _
  have hchild : hsNormSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) ≤
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2 := by
    have h := routePPrimitiveGammaJuliaStokesCofinalChild_hsNorm_le_firstTrace hd
    have hnonneg := hsNorm_nonneg (routePPrimitiveGammaJuliaStokesCofinalChildKernel d)
    have hsq := pow_le_pow_left₀ hnonneg h 2
    simpa only [hsNorm, Real.sq_sqrt
      (hsNormSq_nonneg (routePPrimitiveGammaJuliaStokesCofinalChildKernel d))] using hsq
  rw [hsNorm]
  apply Real.sqrt_le_sqrt
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNormSq_delta_factor hd r]
  exact mul_le_mul_of_nonneg_left hchild ha

theorem continuous_routePPrimitiveGammaJuliaPhysicalStokesHellinger_channel_delta_energy :
    Continuous (fun r : ℝ => ∑ ij : Fin 2 × Fin 2,
      ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r ij.1 ij.2 -
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2) := by
  apply continuous_finsetSum
  rintro ⟨i, j⟩ _
  fin_cases i <;> fin_cases j <;>
    simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel]
  all_goals fun_prop

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_channel_delta_energy_one :
    (∑ ij : Fin 2 × Fin 2,
      ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2 -
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2) = 0 := by
  simp

theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivot_delta_hsNorm :
    Tendsto (fun n : ℕ =>
      hsNorm
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1))
      atTop (nhds 0) := by
  let d : ℕ → ℝ := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence
  let r : ℕ → ℝ := fun n => routePPrimitiveGammaJuliaPhysicalStokesPivotRatio (d n)
  let W : ℕ → ℝ := fun n => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d n)
  let E : ℕ → ℝ := fun n => ∑ ij : Fin 2 × Fin 2,
    ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel (r n) ij.1 ij.2 -
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2
  have hd : ∀ n, 0 < d n := fun n =>
    routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n
  have hr : Tendsto r atTop (nhds 1) := by
    exact tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio.comp
      tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero
  have hW : Tendsto W atTop (nhds 4) := by
    exact tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero
  have hE : Tendsto E atTop (nhds 0) := by
    have h :=
      (continuous_routePPrimitiveGammaJuliaPhysicalStokesHellinger_channel_delta_energy.tendsto 1).comp hr
    simpa only [E, r, Function.comp_def,
      routePPrimitiveGammaJuliaPhysicalStokesHellinger_channel_delta_energy_one] using h
  have hupper : Tendsto (fun n => Real.sqrt (E n * W n ^ 2)) atTop (nhds 0) := by
    have hmul : Tendsto (fun n => E n * W n ^ 2) atTop (nhds 0) := by
      convert hE.mul (hW.pow 2) using 1
      norm_num
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.tendsto 0 |>.comp hmul
  refine squeeze_zero' (Eventually.of_forall fun n => hsNorm_nonneg _) ?_ hupper
  filter_upwards [] with n
  exact routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNorm_delta_le (hd n) (r n)

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_sub :
    TendstoLocallyUniformly
      (fun n z =>
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
                (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z -
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1) z)
      (fun _ => 0) atTop := by
  let d : ℕ → ℝ := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence
  let r : ℕ → ℝ := fun n => routePPrimitiveGammaJuliaPhysicalStokesPivotRatio (d n)
  let W : ℕ → ℝ := fun n => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d n)
  let c : ℕ → ℂ := fun n => (-1 : ℂ) / (8 * (W n : ℂ))
  let A : ℕ → ((Fin 2 × Nat.Primes) × (Fin 2 × Nat.Primes) → ℂ) := fun n =>
    c n • routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) (r n)
  let B : ℕ → ((Fin 2 × Nat.Primes) × (Fin 2 × Nat.Primes) → ℂ) := fun n =>
    c n • routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) 1
  have hd : ∀ n, 0 < d n := fun n =>
    routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n
  have hW : Tendsto W atTop (nhds 4) := by
    exact tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero
  have hWc : Tendsto (fun n => (W n : ℂ)) atTop (nhds (4 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto 4).comp hW
  have hc : Tendsto c atTop (nhds ((-1 : ℂ) / 32)) := by
    have hden : Tendsto (fun n => (8 : ℂ) * (W n : ℂ)) atTop (nhds (32 : ℂ)) := by
      convert tendsto_const_nhds.mul hWc using 1
      norm_num
    change Tendsto ((fun _ : ℕ => (-1 : ℂ)) / (fun n => (8 : ℂ) * (W n : ℂ)))
      atTop (nhds ((-1 : ℂ) / 32))
    exact tendsto_const_nhds.div hden (by norm_num : (32 : ℂ) ≠ 0)
  have hdelta : Tendsto (fun n =>
      hsNorm
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) (r n) -
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) 1))
      atTop (nhds 0) := by
    simpa only [d, r] using tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivot_delta_hsNorm
  have hlim : Tendsto (fun n => hsNorm (A n - B n)) atTop (nhds 0) := by
    have hmul := hc.norm.mul hdelta
    convert hmul using 1
    · ext n
      simp only [A, B, ← smul_sub, HilbertSchmidt.hsNorm_smul]
    · norm_num
  have hA : ∀ n, IsHS (A n) := fun n =>
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS (hd n) (r n)).smul (c n)
  have hB : ∀ n, IsHS (B n) := fun n =>
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS (hd n) 1).smul (c n)
  let C : ℝ := ∑ ij : Fin 2 × Fin 2,
    ‖routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel 1 ij.1 ij.2‖ ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun ij _ => sq_nonneg _
  have hWpos : ∀ n, 0 < W n := fun n =>
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos (hd n)
  have hcNorm : ∀ n, ‖c n‖ = 1 / (8 * W n) := by
    intro n
    dsimp [c]
    rw [norm_div, norm_neg, norm_one, norm_mul]
    norm_num [Complex.norm_real, abs_of_pos (hWpos n)]
  have hBbound : ∀ n, hsNorm (B n) ≤ Real.sqrt C / 8 := by
    intro n
    calc
      hsNorm (B n) = ‖c n‖ *
          hsNorm (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) 1) := by
        change hsNorm (c n •
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel (d n) 1) = _
        rw [HilbertSchmidt.hsNorm_smul]
      _ ≤ ‖c n‖ * (Real.sqrt C * W n) := by
        exact mul_le_mul_of_nonneg_left
          (routePPrimitiveGammaJuliaPhysicalStokesHellinger_hsNorm_le_channel_energy_mul_firstTrace
            (hd n) 1) (norm_nonneg _)
      _ = Real.sqrt C / 8 := by
        rw [hcNorm n]
        field_simp [(hWpos n).ne']
  have hbounded : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M := by
    refine ⟨Real.sqrt C / 8 + 1, by positivity, ?_⟩
    have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsmall] with n hn
    constructor
    · calc
        hsNorm (A n) = hsNorm ((A n - B n) + B n) := by
          congr 1
          ext ij
          simp
        _ ≤ hsNorm (A n - B n) + hsNorm (B n) :=
          hsNorm_add_le (isHS_sub (hA n) (hB n)) (hB n)
        _ ≤ 1 + Real.sqrt C / 8 := by linarith [hBbound n]
        _ = Real.sqrt C / 8 + 1 := by ring
    · exact (hBbound n).trans (by linarith)
  have hmain :=
    GaloisForLFunctions.HTGeometry.tendstoLocallyUniformly_sub_entireDet2_of_hsNorm_sub_tendsto_zero_of_eventually_bound
      A B hA hB hlim hbounded
  simpa only [A, B, c, d, r] using hmain

theorem routePPrimitiveGammaJuliaPhysicalStokesHellinger_balanced_normalized_entireDet2_eq_scaled_ordinary
    (n : ℕ) (z : ℂ) :
    GaloisForLFunctions.HTGeometry.entireDet2
      (((-1 : ℂ) / (8 *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1) z =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
        (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1
        (z / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) := by
  let d := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n
  let W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  let c : ℂ := (-1 : ℂ) / (8 * (W : ℂ))
  have hd : 0 < d := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n
  have hW : (W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  rw [GaloisForLFunctions.HTGeometry.entireDet2_smul
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd 1) c]
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet]
  simp only [sub_self, Complex.ofReal_zero]
  ring_nf
  simp only [Complex.exp_zero, one_mul]
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2]
  change GaloisForLFunctions.HTGeometry.entireDet2
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1) (c * z) =
    GaloisForLFunctions.HTGeometry.entireDet2
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d 1)
      (z * (W : ℂ)⁻¹ * (-1 / 8))
  congr 1
  dsimp only [c]
  field_simp [hW]

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_to_exact_wall :
    TendstoLocallyUniformly
      (fun n z =>
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
                (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z)
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet atTop := by
  let X : ℕ → ℂ → ℂ := fun n z =>
    GaloisForLFunctions.HTGeometry.entireDet2
      (((-1 : ℂ) / (8 *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z
  let Y : ℕ → ℂ → ℂ := fun n z =>
    GaloisForLFunctions.HTGeometry.entireDet2
      (((-1 : ℂ) / (8 *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1) z
  let F : ℂ → ℂ := routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
  change TendstoLocallyUniformly X F atTop
  have hdelta : TendstoLocallyUniformly (fun n z => X n z - Y n z)
      (fun _ => 0) atTop := by
    simpa only [X, Y] using
      tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_sub
  have hbalanced : TendstoLocallyUniformly
      (fun n z =>
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1) z)
      F atTop := by
    apply tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokes_scaledPhysical_apertureSequence.congr
    intro n z
    exact (routePPrimitiveGammaJuliaPhysicalStokesHellinger_balanced_normalized_entireDet2_eq_scaled_ordinary
      n z).symm
  have hsum := hdelta.add hbalanced
  convert hsum using 1
  · funext n z
    change X n z = (X n z - Y n z) + Y n z
    ring
  · funext z
    dsimp only [F]
    simp

theorem routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_eq_scaled_ordinary
    (n : ℕ) (z : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
        (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
        (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))
        (z / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) =
      Complex.exp
        (z * (((1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℝ) : ℂ) / 8)) *
      GaloisForLFunctions.HTGeometry.entireDet2
        (((-1 : ℂ) / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
          routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z := by
  let d := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n
  let r := routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d
  let W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  let c : ℂ := (-1 : ℂ) / (8 * (W : ℂ))
  have hd : 0 < d := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n
  have hW : (W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet]
  rw [GaloisForLFunctions.HTGeometry.entireDet2_smul
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) c]
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2]
  change Complex.exp (z / (8 * (W : ℂ)) * (((1 - r : ℝ) : ℂ) * (W : ℂ))) *
      GaloisForLFunctions.HTGeometry.entireDet2
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r)
        (-(z / (8 * (W : ℂ)))) =
    Complex.exp (z * (((1 - r : ℝ) : ℂ) / 8)) *
      GaloisForLFunctions.HTGeometry.entireDet2
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) (c * z)
  congr 1
  · congr 1
    field_simp [hW]
  · congr 1
    dsimp only [c]
    field_simp [hW]

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_trace_factor :
    TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) =>
        Complex.exp
          (z * (((1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℝ) : ℂ) / 8)))
      (fun _ : ℂ => 1) atTop := by
  let d : ℕ → ℝ := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence
  let r : ℕ → ℝ := fun n => routePPrimitiveGammaJuliaPhysicalStokesPivotRatio (d n)
  have hr : Tendsto r atTop (nhds 1) := by
    exact tendsto_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio.comp
      tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero
  have hrawR : Tendsto (fun n => 1 - r n) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hr using 1
    norm_num
  have hrawC : Tendsto (fun n => ((1 - r n : ℝ) : ℂ)) atTop (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hrawR
  have hphase : Tendsto (fun n => ((1 - r n : ℝ) : ℂ) / 8)
      atTop (nhds 0) := by
    convert hrawC.div_const (8 : ℂ) using 1
    norm_num
  have hexp : TendstoLocallyUniformly
      (fun n (z : ℂ) => Complex.exp (z * (((1 - r n : ℝ) : ℂ) / 8)))
      (fun z : ℂ => Complex.exp (z * 0)) atTop :=
    GaloisForLFunctions.HTGeometry.Interfinity.tendsto_iff_tendstoLocallyUniformly_exp.mp hphase
  simpa only [d, r, mul_zero, Complex.exp_zero] using hexp

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_scaled_ordinary_to_exact_wall :
    TendstoLocallyUniformly
      (fun n z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))
          (z / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))))
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet atTop := by
  have hdet : TendstoLocallyUniformly
      (fun n z =>
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
                (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z)
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet atTop :=
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_to_exact_wall
  have hwall : Continuous routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet :=
    differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet.continuous
  have hprod := GaloisForLFunctions.HTGeometry.tendstoLocallyUniformly_mul
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_trace_factor
    hdet continuous_const hwall
  have hprod' : TendstoLocallyUniformly
      (fun n z =>
        Complex.exp
          (z * (((1 - routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℝ) : ℂ) / 8)) *
        GaloisForLFunctions.HTGeometry.entireDet2
          (((-1 : ℂ) / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) •
            routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
                (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))) z)
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet atTop := by
    simpa using hprod
  apply hprod'.congr
  intro n z
  exact (routePPrimitiveGammaJuliaPhysicalStokesPivot_normalized_entireDet2_eq_scaled_ordinary n z).symm

theorem not_tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_scaled_ordinary_to_normalized_XiC :
    ¬ TendstoLocallyUniformly
      (fun n z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))
          (z / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))))
      (fun z => XiC z / XiC 0) atTop := by
  intro hXi
  have hwall :=
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaPhysicalStokesPivot_scaled_ordinary_to_exact_wall
  have hXiOn : TendstoLocallyUniformlyOn
      (fun n z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))
          (z / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))))
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hXi
  have hwallOn : TendstoLocallyUniformlyOn
      (fun n z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio
            (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n))
          (z / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))))
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hwall
  have hfun : routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet =
      (fun z => XiC z / XiC 0) := by
    funext z
    exact tendsto_nhds_unique
      (hwallOn.tendsto_at (Set.mem_univ z))
      (hXiOn.tendsto_at (Set.mem_univ z))
  have hjet := congrArg (fun f : ℂ → ℂ => iteratedDeriv 2 f 0) hfun
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_two,
    iteratedDeriv_XiC_normalized_two] at hjet
  have hreal := congrArg Complex.re hjet
  norm_num at hreal
  exact thetaCuspNormalizedEvenMoment_one_ne_wallSignedSquareCalibration hreal.symm

end RHTower
