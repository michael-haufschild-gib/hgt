import GaloisForLFunctions.CompletedArithmeticForms.LogarithmicPacketInterpolation

/-!
# Logarithmically weighted center and near cross terms

Prefix estimates are interpolated in conductor size before taking a worst-case
cutoff. The resulting squared bounds retain one individual conductor logarithm.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory SuccessorShellArithmetic ArithmeticIntersectionTheory
  ArithmeticEffectivityTheory ArithmeticElectrostatics BezoutValuationIncidence
  HTGeometry RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis

private theorem conductor_projection_complement_mem {M N : ℕ} (hM : 1 ≤ M)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace M N) :
    u - (conductorSubspace 1 N).starProjection u ∈ conductorSubspace M N ∧
      u - (conductorSubspace 1 N).starProjection u ∈ (conductorSubspace 1 N)ᗮ := by
  constructor
  · exact (conductorSubspace M N).sub_mem hu (conductorSubspace_mono hM N
      ((conductorSubspace 1 N).starProjection_apply_mem u))
  · rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace 1 N).starProjection_inner_eq_zero u v hv

private theorem conductor_one_projection_eq_zero {N : ℕ}
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ (conductorSubspace 1 N)ᗮ) :
    (conductorSubspace 1 N).starProjection u = 0 := by
  let p := (conductorSubspace 1 N).starProjection u
  have hp := (conductorSubspace 1 N).starProjection_apply_mem u
  have h0 : ⟪u, p⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hp hu
  have h1 := (conductorSubspace 1 N).starProjection_inner_eq_zero u p hp
  change ⟪u - p, p⟫ = 0 at h1
  rw [inner_sub_left, h0, real_inner_self_eq_norm_sq] at h1
  have hn : ‖p‖ = 0 := by nlinarith only [h1]
  exact norm_eq_zero.mp hn

/-- The center cross term pays one cutoff logarithm and one coefficient logarithm. -/
theorem fullWeilCenterMatrix_cross_sq_le_logarithmic_weight (α : ℝ)
    {R N : ℕ} (hR : 2 ≤ R) (hRN : R ^ 6 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (a : ℕ → ℝ)
    (hu : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace 1 N)ᗮ)
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hw : w ∈ (conductorSubspace 1 N)ᗮ) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ^ 2 ≤
      (32 * 288 ^ 2 : ℝ) * α ^ 2 * (1 + Real.log R) / Real.log N *
        (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * ‖w‖ ^ 2 := by
  let A := Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
  let P := (conductorSubspace 1 N).starProjection
  let T : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ⟪A (u - P u), w⟫
      map_add' := by
        intro u v
        rw [map_add, show u + v - (P u + P v) = (u - P u) + (v - P v) by abel,
          map_add, inner_add_left]
      map_smul' := by
        intro s u
        simp only [RingHom.id_apply]
        change ⟪A (s • u - P (s • u)), w⟫ = s * ⟪A (u - P u), w⟫
        rw [map_smul, ← smul_sub, map_smul, real_inner_smul_left]
        }
  let C := 288 * |α| / Real.sqrt (Real.log N) * ‖w‖
  have hL : 0 < Real.log N := by
    linarith only [hlog, Real.log_natCast_nonneg R]
  have hsL : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have hprefix : ∀ M : ℕ, 2 ≤ M → M ≤ R → ∀ b : ℕ → ℝ,
      ‖T (∑ m ∈ Icc 1 M, b m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by
    intro M hM hMR b
    let y := ∑ m ∈ Icc 1 M, b m • normalizedRamanujanHorizonVector m N
    let z := y - P y
    have hy : y ∈ conductorSubspace M N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace M N b
    obtain ⟨hz, hz1⟩ := conductor_projection_complement_mem (by omega : 1 ≤ M) hy
    have hM6 : M ^ 6 ≤ N := (Nat.pow_le_pow_left hMR 6).trans hRN
    have hMM : M * M ≤ N := by
      have hp : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      simpa only [sq] using hp.trans hM6
    have hlM : Real.log M ≤ Real.log R := Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMR)
    have hlogM : 18 * (1 + Real.log M) ≤ Real.log N := by linarith only [hlM, hlog]
    have hbnd := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace α hM hM6 hlogM hz hz1 hw
    have hframe := (half_and_three_halves_riesz_of_log_le hM hMM hlogM b).2
    have hpy := norm_starProjection_sq_add_sub_sq (conductorSubspace 1 N) y
    have hzsq : ‖z‖ ^ 2 ≤ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by
      have hm0 : 0 ≤ ∑ m ∈ Icc 1 M, b m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      change ‖P y‖ ^ 2 + ‖z‖ ^ 2 = ‖y‖ ^ 2 at hpy
      change ‖y‖ ^ 2 ≤ _ at hframe
      linarith only [hpy, hframe, sq_nonneg ‖P y‖, hm0]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hbnd 2
    change ‖T y‖ ^ 2 ≤ _
    change |⟪A z, w⟫| ^ 2 ≤ _
    calc
      _ ≤ (144 * |α| * (1 + Real.log M) / Real.sqrt (Real.log N) * ‖z‖ * ‖w‖) ^ 2 := hs
      _ = (144 ^ 2 * α ^ 2 * (1 + Real.log M) ^ 2 / Real.log N * ‖w‖ ^ 2) * ‖z‖ ^ 2 := by
        rw [mul_pow, mul_pow, div_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hL.le]
        ring
      _ ≤ (144 ^ 2 * α ^ 2 * (1 + Real.log M) ^ 2 / Real.log N * ‖w‖ ^ 2) *
          (2 * ∑ m ∈ Icc 1 M, b m ^ 2) := mul_le_mul_of_nonneg_left hzsq (by positivity)
      _ ≤ C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by
        dsimp only [C]
        rw [mul_pow, div_pow, mul_pow, sq_abs, Real.sq_sqrt hL.le]
        have hn : 0 ≤ α ^ 2 * (1 + Real.log M) ^ 2 / Real.log N * ‖w‖ ^ 2 *
            (∑ m ∈ Icc 1 M, b m ^ 2) := by positivity
        calc
          _ = (2 * 144 ^ 2 : ℝ) * (α ^ 2 * (1 + Real.log M) ^ 2 /
              Real.log N * ‖w‖ ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2) := by ring
          _ ≤ 288 ^ 2 * (α ^ 2 * (1 + Real.log M) ^ 2 /
              Real.log N * ‖w‖ ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) hn
          _ = _ := by ring
  have h := conductor_packet_sq_le_logarithmic_weight hR T C hprefix a
  have hP0 := conductor_one_projection_eq_zero hu
  change |⟪A ((∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) -
    P (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N)), w⟫| ^ 2 ≤ _ at h
  change P (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) = 0 at hP0
  rw [hP0, sub_zero] at h
  exact h.trans_eq (by
    dsimp only [C]
    rw [mul_pow, div_pow, mul_pow, sq_abs, Real.sq_sqrt hL.le]
    ring)

private def finiteDownwardPrimeMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ := fun n j =>
  (∑ k ∈ range (lagRange (Real.log N + c / N + 1)),
    _root_.RHTower.vonMangoldtAtom k *
      (if (n : ℕ) = k * j then 0 else bumpCorr (atomDilate φ (c / N))
        (Real.log k - (Real.log (n : ℕ) - Real.log (j : ℕ))))) /
    ∫ u, atomDilate φ (c / N) u ^ 2

private theorem finiteDownwardPrimeMatrix_apply {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (finiteDownwardPrimeMatrix φ c N) u = downwardPrimeVector φ c N u := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp (div_pos hc hNR)
  ext n
  change (∑ j : PrimeHorizonIndex N, finiteDownwardPrimeMatrix φ c N n j * u j) =
    downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension u) n /
      (∫ t, atomDilate φ (c / N) t ^ 2)
  rw [downwardPrimeRow_eq_sum hgsupp (div_nonneg hc.le hNR.le) n.property]
  let K := lagRange (Real.log N + c / N + 1)
  let G := ∫ t, atomDilate φ (c / N) t ^ 2
  let b := fun k j => if (n : ℕ) = k * j then 0 else bumpCorr (atomDilate φ (c / N))
    (Real.log k - (Real.log (n : ℕ) - Real.log j))
  have hrow : (∑ j : PrimeHorizonIndex N, finiteDownwardPrimeMatrix φ c N n j * u j) =
      ∑ j ∈ Icc 1 N, ((∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * b k j) / G) *
        primeHorizonExtension u j := by
    rw [← sum_coe_sort (Icc 1 N) (fun j =>
      ((∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * b k j) / G) * primeHorizonExtension u j)]
    exact sum_congr rfl fun j _ => by rw [primeHorizonExtension_coe]; rfl
  rw [hrow]
  change (∑ j ∈ Icc 1 N, ((∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * b k j) / G) *
    primeHorizonExtension u j) =
      (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
        ∑ j ∈ Icc 1 N, primeHorizonExtension u j * b k j) / G
  simp only [sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring

/-- The near cross norm retains individual conductor logarithms. -/
theorem exists_overlap_sub_downward_sq_le_logarithmic_weight {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hφM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R * R ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N → ∀ a : ℕ → ℝ,
      ‖Matrix.toEuclideanLin (overlapMatrix φ c N)
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) -
        downwardPrimeVector φ c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        C * c ^ 4 * (1 + Real.log R) *
          ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N)) *
            ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace hφ hsupp hφM
  refine ⟨256 * C₀ ^ 2, by positivity, ?_⟩
  intro R N c hR hRN hlog hc hw hrad a
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  let s := Real.sqrt ((1 + Real.log c) / Real.log N)
  let r := Real.sqrt (Real.log N / N)
  let C := 2 * C₀ * c ^ 2 * (s + (R : ℝ) * r)
  let T : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ] EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    Matrix.toEuclideanLin (overlapMatrix φ c N) - Matrix.toEuclideanLin (finiteDownwardPrimeMatrix φ c N)
  have hT (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
      T u = Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u := by
    change Matrix.toEuclideanLin (overlapMatrix φ c N) u -
      Matrix.toEuclideanLin (finiteDownwardPrimeMatrix φ c N) u = _
    rw [finiteDownwardPrimeMatrix_apply hφ hsupp hc0 hN]
  have hprefix : ∀ M : ℕ, 2 ≤ M → M ≤ R → ∀ b : ℕ → ℝ,
      ‖T (∑ m ∈ Icc 1 M, b m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by
    intro M hM hMR b
    let u := ∑ m ∈ Icc 1 M, b m • normalizedRamanujanHorizonVector m N
    have hMM : M * M ≤ N := (Nat.mul_le_mul hMR hMR).trans hRN
    have hlM : Real.log M ≤ Real.log R := Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMR)
    have hlogM : 18 * (1 + Real.log M) ≤ Real.log N := by linarith only [hlM, hlog]
    have hMrad : ((M * M : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
      apply le_trans _ hrad
      apply mul_le_mul_of_nonneg_right _ (by unfold linearNearRowRadius; positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul hMR hMR) 1
    have hraw := hbound hM hMM hlogM hc hw hMrad
      (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace M N b)
    have hframe := (half_and_three_halves_riesz_of_log_le hM hMM hlogM b).2
    have hH1 : 1 ≤ 1 + Real.log M := by linarith only [Real.log_natCast_nonneg M]
    have hcoef : C₀ * (c ^ 2 * (1 + Real.log M) * s + c ^ 2 * (M : ℝ) * r) ≤
        (C / 2) * (1 + Real.log M) := by
      have hmR : (M : ℝ) ≤ R := by exact_mod_cast hMR
      have hRH := mul_le_mul_of_nonneg_left hH1 (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
      have hh := mul_le_mul_of_nonneg_left (hmR.trans (by simpa only [mul_one] using hRH))
        (show 0 ≤ C₀ * c ^ 2 * r by positivity)
      dsimp only [C]
      nlinarith only [hh]
    have hnorm : ‖T u‖ ≤ (C / 2) * (1 + Real.log M) * ‖u‖ := by
      rw [hT]
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hmass : 0 ≤ ∑ m ∈ Icc 1 M, b m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    change ‖u‖ ^ 2 ≤ _ at hframe
    change ‖T u‖ ^ 2 ≤ _
    have hf := mul_le_mul_of_nonneg_left hframe (sq_nonneg ((C / 2) * (1 + Real.log M)))
    have hnn : 0 ≤ C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by positivity
    nlinarith only [hs, hf, hnn]
  have h := conductor_packet_sq_le_logarithmic_weight hR T C hprefix a
  rw [hT] at h
  have hs2 : s ^ 2 = (1 + Real.log c) / Real.log N := Real.sq_sqrt (by
    have hlc := Real.log_nonneg hc
    positivity)
  have hr2 : r ^ 2 = Real.log N / N := Real.sq_sqrt (by positivity)
  have hsum : (s + (R : ℝ) * r) ^ 2 ≤
      2 * ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N)) := by
    nlinarith only [sq_nonneg (s - (R : ℝ) * r), hs2, hr2]
  have hG : 0 ≤ ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_nonneg fun m _ => mul_nonneg (by positivity) (sq_nonneg _)
  have hfactor : 0 ≤ 128 * C₀ ^ 2 * c ^ 4 * (1 + Real.log R) *
      (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) := by positivity
  apply h.trans
  have hm := mul_le_mul_of_nonneg_left hsum hfactor
  dsimp only [C]
  nlinarith only [hm]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullWeilCenterMatrix_cross_sq_le_logarithmic_weight
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_overlap_sub_downward_sq_le_logarithmic_weight
