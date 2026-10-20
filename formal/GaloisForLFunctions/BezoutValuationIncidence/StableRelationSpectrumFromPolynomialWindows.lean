import GaloisForLFunctions.BezoutValuationIncidence.ParsevalForTranslatedMomentArrays
import GaloisForLFunctions.BezoutValuationIncidence.ExactOrderOfTheMomentTransferHierarchy

/-!
# Stable recovery of the relation spectrum from polynomial windows

The degree-`m` window averages of a row at any phase approximate its period moments within
`(e^{19/4} N)^m Q_Sel^{m/2} / K`, and the period moment array is an isometry of the relation
spectrum `(Π_i Y(ord ζ_i))_{Π ζ_i = 1}` (Parseval over shift vectors). Consequently, if two rows have
degree-`m` window averages within `η` of each other for every shift vector — read on windows of
length `K` at arbitrary, shift-dependent phases — then their relation spectra are `ℓ²`-close:

`‖A_c - A_{c'}‖₂ ≤ η + (e^{19/4} N)^m (Q_c^{m/2} + Q_{c'}^{m/2}) / K`.

The constants do not depend on `N` once `K` exceeds a fixed multiple of `N^m`: polynomial windows
recover the relation spectrum stably. At degree two the relation spectrum is the Selberg magnitude
profile, `‖A_c - A_{c'}‖₂² = Σ_q φ(q) (Y_c(q)² - Y_{c'}(q)²)²`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The window average of a degree-`m` translated product. -/
def windowMoment (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (v : Fin m → ℕ) (A K : ℕ) : ℝ :=
  (∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) / K

/-- The transfer error of a window average. -/
def windowTransferError (N m K : ℕ) (c : ℕ → ℝ) : ℝ :=
  (Real.exp (19 / 4) * N) ^ m * Real.sqrt (selbergTotientDiagonalForm N c) ^ m / K

theorem abs_windowMoment_sub_le (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (v : Fin m → ℕ) (A : ℕ) {K : ℕ}
    (hK : 0 < K) :
    |windowMoment N c v A K - SieveMoments.translatedMoment N c v| ≤
      windowTransferError N m K c := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have h := isTranslatedMomentTransferConstant_exp_mul N m c v A K
  rw [windowMoment, windowTransferError, le_div_iff₀ hKR]
  calc |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) / K -
        SieveMoments.translatedMoment N c v| * K
      = |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
          K * SieveMoments.translatedMoment N c v| := by
        rw [← abs_of_pos hKR, ← abs_mul, abs_of_pos hKR, sub_mul, div_mul_cancel₀ _ hKR.ne',
          mul_comm]
    _ ≤ _ := by simpa only [mul_assoc] using h

/-- **Stable recovery of the relation spectrum.** -/
theorem sqrt_relation_energy_le_of_windows (N m : ℕ) {K : ℕ} (hK : 0 < K) (c c' : ℕ → ℝ)
    (φ ψ : (Fin m → ℕ) → ℕ) {η : ℝ}
    (hobs : ∀ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
      |windowMoment N c v (φ v) K - windowMoment N c' v (ψ v) K| ≤ η) :
    Real.sqrt (∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ - relationCoeff N c' ζ) ^ 2) ≤
      η + (windowTransferError N m K c + windowTransferError N m K c') := by
  classical
  set B := η + (windowTransferError N m K c + windowTransferError N m K c')
  set V := Fintype.piFinset (fun _ : Fin m => range N.factorial)
  have hpt : ∀ v ∈ V, |SieveMoments.translatedMoment N c v -
      SieveMoments.translatedMoment N c' v| ≤ B := by
    intro v hv
    have h1 := abs_windowMoment_sub_le N c v (φ v) hK
    have h2 := abs_windowMoment_sub_le N c' v (ψ v) hK
    have h3 := hobs v hv
    have e : SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N c' v =
        (SieveMoments.translatedMoment N c v - windowMoment N c v (φ v) K) +
          (windowMoment N c v (φ v) K - windowMoment N c' v (ψ v) K) +
          (windowMoment N c' v (ψ v) K - SieveMoments.translatedMoment N c' v) := by ring
    rw [e]
    rw [abs_sub_comm] at h1
    calc |(SieveMoments.translatedMoment N c v - windowMoment N c v (φ v) K) +
          (windowMoment N c v (φ v) K - windowMoment N c' v (ψ v) K) +
          (windowMoment N c' v (ψ v) K - SieveMoments.translatedMoment N c' v)|
        ≤ |SieveMoments.translatedMoment N c v - windowMoment N c v (φ v) K| +
          |windowMoment N c v (φ v) K - windowMoment N c' v (ψ v) K| +
          |windowMoment N c' v (ψ v) K - SieveMoments.translatedMoment N c' v| :=
          (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ B := by linarith
  have hB0 : 0 ≤ B := by
    have hmem : (fun _ : Fin m => 0) ∈ V :=
      Fintype.mem_piFinset.mpr fun _ => mem_range.mpr (Nat.factorial_pos N)
    exact (abs_nonneg _).trans (hpt _ hmem)
  have hP : (0 : ℝ) < (N.factorial : ℝ) ^ m := by positivity
  have hsum : ∑ v ∈ V, (SieveMoments.translatedMoment N c v -
      SieveMoments.translatedMoment N c' v) ^ 2 ≤ (N.factorial : ℝ) ^ m * B ^ 2 := by
    calc ∑ v ∈ V, (SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N c' v) ^ 2
        ≤ ∑ _v ∈ V, B ^ 2 := sum_le_sum fun v hv => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hpt v hv) 2
      _ = (N.factorial : ℝ) ^ m * B ^ 2 := by
          rw [sum_const, Fintype.card_piFinset, prod_const, card_range, card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [sum_sq_translatedMoment_sub_eq] at hsum
  have hrel : ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ - relationCoeff N c' ζ) ^ 2 ≤
      B ^ 2 := le_of_mul_le_mul_left hsum hP
  calc Real.sqrt (∑ ζ ∈ zeroProductTuples N m,
        (relationCoeff N c ζ - relationCoeff N c' ζ) ^ 2)
      ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hrel
    _ = B := Real.sqrt_sq hB0

/-! ## Degree two: the Selberg magnitude profile -/

theorem inv_mem_responseRoots {N : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots N) :
    ζ⁻¹ ∈ responseRoots N := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  refine mem_biUnion.mpr ⟨d, hd, ?_⟩
  have hd0 := (mem_Icc.mp hd).1
  rw [Polynomial.mem_nthRootsFinset hd0] at hζd ⊢
  rw [inv_pow, hζd, inv_one]

theorem orderOf_inv_of_mem_responseRoots {N : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots N) :
    orderOf ζ⁻¹ = orderOf ζ := by
  have hn := norm_eq_one_of_mem_responseRoots hζ
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [inv_pow, inv_eq_one]

/-- At degree two the relation energy is the totient-weighted distance of the magnitude profiles. -/
theorem relation_energy_two_eq (N : ℕ) (c c' : ℕ → ℝ) :
    ∑ ζ ∈ zeroProductTuples N 2, (relationCoeff N c ζ - relationCoeff N c' ζ) ^ 2 =
      ∑ q ∈ Icc 1 N, (q.totient : ℝ) *
        (selbergMultiplesCoord N c q ^ 2 - selbergMultiplesCoord N c' q ^ 2) ^ 2 := by
  classical
  rw [← sum_responseRoots_orderOf N (fun q =>
    (selbergMultiplesCoord N c q ^ 2 - selbergMultiplesCoord N c' q ^ 2) ^ 2)]
  refine sum_nbij' (fun τ => τ 0) (fun ζ => ![ζ, ζ⁻¹]) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    exact (Fintype.mem_piFinset.mp (mem_filter.mp hτ).1) 0
  · intro ζ hζ
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · fin_cases i
      · exact hζ
      · exact inv_mem_responseRoots hζ
    · have hn := norm_eq_one_of_mem_responseRoots hζ
      have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact zero_ne_one hn
      simp [Fin.prod_univ_two, hζ0]
  · intro τ hτ
    have hprod := (mem_filter.mp hτ).2
    rw [Fin.prod_univ_two] at hprod
    funext i
    fin_cases i
    · rfl
    · exact (eq_inv_of_mul_eq_one_right hprod).symm
  · intro ζ _
    rfl
  · intro τ hτ
    have hprod := (mem_filter.mp hτ).2
    rw [Fin.prod_univ_two] at hprod
    have h1 : τ 1 = (τ 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hτ0 := (Fintype.mem_piFinset.mp (mem_filter.mp hτ).1) 0
    unfold relationCoeff
    rw [Fin.prod_univ_two, Fin.prod_univ_two, h1, orderOf_inv_of_mem_responseRoots hτ0]
    ring

/-- **Stable two-point spectrum from polynomial windows.** -/
theorem sqrt_magnitude_profile_distance_le_of_windows (N : ℕ) {K : ℕ} (hK : 0 < K)
    (c c' : ℕ → ℝ) (φ ψ : (Fin 2 → ℕ) → ℕ) {η : ℝ}
    (hobs : ∀ v ∈ Fintype.piFinset (fun _ : Fin 2 => range N.factorial),
      |windowMoment N c v (φ v) K - windowMoment N c' v (ψ v) K| ≤ η) :
    Real.sqrt (∑ q ∈ Icc 1 N, (q.totient : ℝ) *
        (selbergMultiplesCoord N c q ^ 2 - selbergMultiplesCoord N c' q ^ 2) ^ 2) ≤
      η + (windowTransferError N 2 K c + windowTransferError N 2 K c') := by
  rw [← relation_energy_two_eq]
  exact sqrt_relation_energy_le_of_windows N 2 hK c c' φ ψ hobs

end

end GaloisForLFunctions.BezoutValuationIncidence
