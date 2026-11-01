import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.PrimePolynomialSelfAbsorption
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit

/-!
# Finite-Defect Stratum and Logarithmic Zero-Free Corridor Classification

Complete classification of uniform unit-window prime-polynomial and constant bounds on the Hecke
defect `heckeDefect (baseTwistTest γ) (c * Real.log T)` across `[T, T + 1)`:

1. **Super-polynomial rapid decay on the finite-off-line stratum (`FiniteOffLine`)**
   (`exists_heckeDefect_log_le_div_pow_of_finiteOffLine`,
    `exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine`,
    `exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine`):
   Under `FiniteOffLine` (the first rung of `index_exit_first_rung_tfae`), all off-line zeros of `ζ`
   have bounded height, reducing `heckeDefect (baseTwistTest γ) L` to a fixed finite sum for all
   `(γ, L)`. All-order Paley–Wiener rapid decay of `baseBump` forces
   `heckeDefect (baseTwistTest γ) (c * log T) ≤ C_{c, N} / T^N` for every `c > 0` and `N : ℕ`,
   uniformly on `T ≥ 2`, `γ ∈ [T, T + 1)`. Consequently, at any fixed `c > 0`, both the modulus
   prime-polynomial bound (for arbitrary prime cutoff `M : ℝ → ℕ`, including `⌊T^{2c}⌋₊` and
   `N*(c log T)`) and the signed `-α Re Π_{F_{c log T}} + C'` bound hold globally on `[2, ∞)`
   without implying `RiemannHypothesis`.

2. **All-`c` scale transfer, 5-way TFAE, and positive-sign separation**
   (`unitWindowDepthCharge_log_iff_of_pos`, `heckeDefect_log_unitWindow_tfae`,
    `eventually_heckeDefect_le_pos_re_primePolynomial_iff`):
   Unit-window self-absorption (`Theorem 1a`) collapses the prime polynomial `Π_{F_{c log T}}` out
   of the Route `WD` question, proving that for every `c > 0` and `α ≥ 0` the uniform modulus bound,
   uniform `-α Re Π_{F_L}` bound, uniform `O(1)` bound on `E_γ(c log T)`, unit-window `L¹` bound,
   and unit-window depth-charge bound are 5-way equivalent (`TFAE`) and independent of `c > 0`.
   By contrast, for `α > 0`, the opposite-sign bound `E_γ(c log T) ≤ +α Re Π_{F_L} + C` holds iff
   both `E_γ(c log T) = O(1)` and `collidedForm zetaZeroConfig (twist γ F_{c log T}) = O(1)` (which
   forces bounded horizontal fibre multiplicity `H(γ) = O(1)`).

3. **Unconditional logarithmic zero-free corridor, `ZerosApproachLine`, and `LindelofCriticalLine`**
   (`exists_log_zeroFree_corridor_of_heckeDefect_bound`,
    `zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`):
   Any equivalent condition of the 5-way TFAE forces an explicit classical logarithmic zero-free
   corridor `|ρ.re - 1/2| ≤ A / log |ρ.im|` across the critical strip, hence `ZerosApproachLine`,
   `OffLineSparse`, `LindelofCriticalLine`, and `∃ β < 1/2, XiZeroHalfPlaneBound β`, together with
   `ΔO(T) ≪ log T` under bounded `-Re Π_{F_L}`.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23
open _root_.RHTower.DeBruijn _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse
open _root_.RHTower.CosineSparseCluster _root_.RHTower.CosineDefectBudget

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ArithmeticOrientationGeometry
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Elementary `depthKernel` exponential cap and `unitWindowDepthCharge` -/

/-- For `L ≥ 0` and `|d| ≤ 1 / 2`, `depthKernel L d ≤ exp L`. -/
theorem depthKernel_le_exp_of_abs_le_half {L d : ℝ} (hL : 0 ≤ L) (hd : |d| ≤ 1 / 2) :
    depthKernel L d ≤ Real.exp L := by
  have hmono : depthKernel L d ≤ depthKernel L (1 / 2) :=
    depthKernel_mono_depth L (by simpa using hd)
  refine hmono.trans ?_
  have hsinh : depthKernel L (1 / 2) = (Real.exp (L / 2) - Real.exp (-(L / 2))) ^ 2 := by
    rw [depthKernel_eq_four_sinh_sq, show (1 / 2 : ℝ) * L = L / 2 by ring, Real.sinh_eq]
    ring
  rw [hsinh]
  have he_pos : 0 < Real.exp (-(L / 2)) := Real.exp_pos _
  have he_le1 : Real.exp (-(L / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1_le : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by linarith)
  have hsub_nn : 0 ≤ Real.exp (L / 2) - Real.exp (-(L / 2)) := by linarith
  have hsub_le : Real.exp (L / 2) - Real.exp (-(L / 2)) ≤ Real.exp (L / 2) := by linarith
  calc (Real.exp (L / 2) - Real.exp (-(L / 2))) ^ 2
      ≤ Real.exp (L / 2) ^ 2 := pow_le_pow_left₀ hsub_nn hsub_le 2
    _ = Real.exp L := by rw [sq, ← Real.exp_add]; congr 1; ring

/-- Unit-window hyperbolic depth charge `∑_{ρ ∈ W(T)} ord_ξ(ρ) depthKernel L (Re ρ - 1/2)`. -/
def unitWindowDepthCharge (T L : ℝ) : ℝ :=
  ∑ ρ ∈ xiUnitWindowZeros T,
    ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2)

theorem unitWindowDepthCharge_nonneg (T L : ℝ) : 0 ≤ unitWindowDepthCharge T L :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)

theorem depthKernel_le_unitWindowDepthCharge {T L : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiUnitWindowZeros T) :
    depthKernel L (ρ.re - 1 / 2) ≤ unitWindowDepthCharge T L := by
  obtain ⟨hS, _⟩ := mem_xiUnitWindowZeros.mp hρ
  have hxi : xi ρ = 0 := ((Set.Finite.mem_toFinset _).mp hS).2
  have hord1 : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hxi)
  calc depthKernel L (ρ.re - 1 / 2)
      = 1 * depthKernel L (ρ.re - 1 / 2) := (one_mul _).symm
    _ ≤ ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2) :=
        mul_le_mul_of_nonneg_right hord1 (depthKernel_nonneg _ _)
    _ ≤ unitWindowDepthCharge T L :=
        Finset.single_le_sum
          (f := fun z => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2))
          (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) hρ

/-! ## §2. Theorem 2 — Super-polynomial decay and prime-polynomial bounds under `FiniteOffLine` -/

/-- Under `FiniteOffLine`, there exist `R₀ > 0` and a finite subset
`S_off : Finset zetaZeroConfig.carrier` with `∀ ρ ∈ S_off, |(ρ : ℂ).im| ≤ R₀` such that for all
`γ, L ∈ ℝ`, `heckeDefect (baseTwistTest γ) L` equals the finite sum over `S_off`. -/
theorem exists_finset_heckeDefect_eq_sum_of_finiteOffLine (hF : FiniteOffLine) :
    ∃ (R₀ : ℝ) (S_off : Finset zetaZeroConfig.carrier),
      0 < R₀ ∧ (∀ ρ ∈ S_off, |(ρ : ℂ).im| ≤ R₀) ∧
      ∀ γ L : ℝ, heckeDefect (baseTwistTest γ) L =
        ∑ ρ ∈ S_off, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) := by
  classical
  obtain ⟨T₀, hT₀⟩ := finiteOffLine_iff_exists_onLine_above.mp hF
  set R₀ : ℝ := |T₀| + 1
  have hR₀_pos : 0 < R₀ := by dsimp [R₀]; positivity
  let S₀ : Finset ℂ := (zetaZeroConfig.finite_window (-R₀ - 1) R₀).toFinset
  let emb : {z // z ∈ S₀} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, ((Set.Finite.mem_toFinset _).mp z.2).1⟩
  let S_off : Finset zetaZeroConfig.carrier := S₀.attach.image emb
  refine ⟨R₀ + 1, S_off, by positivity, ?_, fun γ L => ?_⟩
  · intro ρ hρ
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨_, h1, h2⟩ := (Set.Finite.mem_toFinset _).mp z.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine tsum_eq_sum fun ρ hρ_not => ?_
    have hgt : R₀ < |(ρ : ℂ).im| := by
      by_contra hle
      have habs := abs_le.mp (not_lt.mp hle)
      have hz : (ρ : ℂ) ∈ S₀ := (Set.Finite.mem_toFinset _).mpr ⟨ρ.2, by linarith [habs.1], habs.2⟩
      exact hρ_not (Finset.mem_image.mpr ⟨⟨(ρ : ℂ), hz⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
    have hT₀_lt : T₀ < |(ρ : ℂ).im| := lt_of_le_of_lt (by dsimp [R₀]; linarith [le_abs_self T₀]) hgt
    have hre : (ρ : ℂ).re = 1 / 2 := hT₀ (ρ : ℂ) ρ.2 hT₀_lt
    have hd0 : zetaDepth ρ = 0 := by simp [zetaDepth, hre]
    rw [hd0, depthKernel_zero_depth, mul_zero]

/-- **Theorem 2a (`exists_heckeDefect_log_le_div_pow_of_finiteOffLine` — Super-Polynomial Decay on
the `FiniteOffLine` Stratum).**
Under `FiniteOffLine`, for every `c > 0` and every `N : ℕ`, there exists `C > 0` such that for all
`T ≥ 2` and all `γ ∈ [T, T + 1)`, `heckeDefect (baseTwistTest γ) (c * log T) ≤ C / T ^ N`. -/
theorem exists_heckeDefect_log_le_div_pow_of_finiteOffLine (hF : FiniteOffLine)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ C / T ^ N := by
  obtain ⟨R₀, S_off, hR₀_pos, hS_im, hsum_eq⟩ := exists_finset_heckeDefect_eq_sum_of_finiteOffLine hF
  set K : ℕ := N + ⌈c⌉₊ + 1
  obtain ⟨C_K, hCK, hpw⟩ := exists_norm_tr_twist_baseBump_le_pow K
  set M_mult : ℝ := ∑ ρ ∈ S_off, (zetaZeroConfig.mult ρ : ℝ)
  have hM_nn : 0 ≤ M_mult := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  set T₁ : ℝ := 2 * R₀ + 2
  set C_low : ℝ := (M_mult + 1) * Real.exp (1 / 4) * Real.exp (c * Real.log T₁) * T₁ ^ N
  set C_high : ℝ := (M_mult + 1) * (2 ^ K * C_K) ^ 2
  refine ⟨C_low + C_high + 1, by positivity, fun T hT2 γ hγ => ?_⟩
  rw [hsum_eq γ (c * Real.log T)]
  have hT_pos : 0 < T := by linarith
  have hTN_pos : 0 < T ^ N := pow_pos hT_pos N
  have hL_nn : 0 ≤ c * Real.log T := mul_nonneg hc.le (Real.log_nonneg (by linarith))
  rcases le_or_gt T T₁ with hT_le | hT_gt
  · -- Bounded regime `2 ≤ T ≤ T₁`: uniform finite-sum cap
    have hterm : ∀ ρ ∈ S_off,
        zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (1 / 4) * Real.exp (c * Real.log T₁)) := by
      intro ρ _
      have hb : Complex.normSq (tr (twist γ baseBump) ρ) ≤ Real.exp (1 / 4) := by
        rw [Complex.normSq_eq_norm_sq]
        refine (pow_le_pow_left₀ (norm_nonneg _)
          (norm_tr_twist_baseBump_le_exp γ (abs_zetaDepth_le ρ)) 2).trans_eq ?_
        rw [← Real.exp_nat_mul]; norm_num
      have hdk : depthKernel (c * Real.log T) (zetaDepth ρ) ≤ Real.exp (c * Real.log T₁) := by
        refine (depthKernel_le_exp_of_abs_le_half hL_nn (abs_zetaDepth_le ρ)).trans ?_
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (Real.log_le_log hT_pos hT_le) hc.le)
      dsimp [zetaWeight, baseTwistTest]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
            depthKernel (c * Real.log T) (zetaDepth ρ)
          = (zetaZeroConfig.mult ρ : ℝ) *
              (Complex.normSq (tr (twist γ baseBump) ρ) *
                depthKernel (c * Real.log T) (zetaDepth ρ)) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (1 / 4) * Real.exp (c * Real.log T₁)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hb hdk (depthKernel_nonneg _ _)
              (Real.exp_pos _).le) (Nat.cast_nonneg _)
    have hsum_le : ∑ ρ ∈ S_off,
        zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (M_mult + 1) * Real.exp (1 / 4) * Real.exp (c * Real.log T₁) := by
      calc ∑ ρ ∈ S_off, zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ)
          ≤ ∑ ρ ∈ S_off, (zetaZeroConfig.mult ρ : ℝ) *
              (Real.exp (1 / 4) * Real.exp (c * Real.log T₁)) := Finset.sum_le_sum hterm
        _ = M_mult * (Real.exp (1 / 4) * Real.exp (c * Real.log T₁)) := by
            rw [← Finset.sum_mul]
        _ ≤ (M_mult + 1) * Real.exp (1 / 4) * Real.exp (c * Real.log T₁) := by
            have : 0 ≤ Real.exp (1 / 4) * Real.exp (c * Real.log T₁) := by positivity
            nlinarith
    have hratio : 1 ≤ T₁ ^ N / T ^ N :=
      (one_le_div hTN_pos).mpr (pow_le_pow_left₀ hT_pos.le hT_le N)
    have hCh_nn : 0 ≤ C_high := by dsimp [C_high]; positivity
    calc ∑ ρ ∈ S_off, zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ)
        ≤ ((M_mult + 1) * Real.exp (1 / 4) * Real.exp (c * Real.log T₁)) * (T₁ ^ N / T ^ N) :=
          hsum_le.trans (le_mul_of_one_le_right (by positivity) hratio)
      _ = C_low / T ^ N := by dsimp [C_low]; ring
      _ ≤ (C_low + C_high + 1) / T ^ N :=
          div_le_div_of_nonneg_right (by linarith) hTN_pos.le
  · -- High-ordinate regime `T > 2 R₀ + 2`: `|ρ.im - γ| ≥ T / 2` for every `ρ ∈ S_off`
    have hterm : ∀ ρ ∈ S_off,
        zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (zetaZeroConfig.mult ρ : ℝ) * ((2 ^ K * C_K) ^ 2 / T ^ N) := by
      intro ρ hρ
      have him_le : (ρ : ℂ).im ≤ R₀ := (abs_le.mp (hS_im ρ hρ)).2
      have hsep : T / 2 ≤ |(ρ : ℂ).im - γ| := by
        have hdiff : T / 2 ≤ γ - (ρ : ℂ).im := by dsimp [T₁] at hT_gt; linarith [hγ.1]
        rw [abs_sub_comm]
        exact hdiff.trans (le_abs_self _)
      have hne : (ρ : ℂ).im ≠ γ := by
        intro heq; rw [heq, sub_self, abs_zero] at hsep; linarith
      have hpw_ρ := hpw γ ρ (abs_zetaDepth_le ρ) hne
      have hTK_pos : (0 : ℝ) < (T / 2) ^ K := by positivity
      have hnorm_le : ‖tr (twist γ baseBump) ρ‖ ≤ (2 ^ K * C_K) / T ^ K := by
        calc ‖tr (twist γ baseBump) ρ‖
            ≤ C_K / |(ρ : ℂ).im - γ| ^ K := hpw_ρ
          _ ≤ C_K / (T / 2) ^ K :=
              div_le_div_of_nonneg_left hCK.le hTK_pos (pow_le_pow_left₀ (by positivity) hsep K)
          _ = (2 ^ K * C_K) / T ^ K := by rw [div_pow]; field_simp
      have hnsq_le : Complex.normSq (tr (twist γ baseBump) ρ) ≤ (2 ^ K * C_K) ^ 2 / T ^ (2 * K) := by
        rw [Complex.normSq_eq_norm_sq]
        refine (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2).trans_eq ?_
        rw [div_pow, ← pow_mul, mul_comm K 2]
      have hdk_le : depthKernel (c * Real.log T) (zetaDepth ρ) ≤ T ^ ⌈c⌉₊ := by
        refine (depthKernel_le_exp_of_abs_le_half hL_nn (abs_zetaDepth_le ρ)).trans ?_
        calc Real.exp (c * Real.log T)
            ≤ Real.exp ((⌈c⌉₊ : ℝ) * Real.log T) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (Real.log_nonneg (by linarith)))
          _ = T ^ ⌈c⌉₊ := by rw [Real.exp_nat_mul, Real.exp_log hT_pos]
      have hpow_le : T ^ N * T ^ ⌈c⌉₊ ≤ T ^ (2 * K) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by linarith : 1 ≤ T) (by dsimp [K]; omega)
      have hprod_le : ((2 ^ K * C_K) ^ 2 / T ^ (2 * K)) * T ^ ⌈c⌉₊ ≤ (2 ^ K * C_K) ^ 2 / T ^ N := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hT_pos (2 * K)) hTN_pos]
        have : (2 ^ K * C_K) ^ 2 * T ^ ⌈c⌉₊ * T ^ N = (2 ^ K * C_K) ^ 2 * (T ^ N * T ^ ⌈c⌉₊) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow_le (sq_nonneg _)
      dsimp [zetaWeight, baseTwistTest]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
            depthKernel (c * Real.log T) (zetaDepth ρ)
          = (zetaZeroConfig.mult ρ : ℝ) *
              (Complex.normSq (tr (twist γ baseBump) ρ) *
                depthKernel (c * Real.log T) (zetaDepth ρ)) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (((2 ^ K * C_K) ^ 2 / T ^ (2 * K)) * T ^ ⌈c⌉₊) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hnsq_le hdk_le (depthKernel_nonneg _ _) (by positivity))
              (Nat.cast_nonneg _)
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ((2 ^ K * C_K) ^ 2 / T ^ N) :=
            mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg _)
    have hCl_nn : 0 ≤ C_low := by dsimp [C_low]; positivity
    calc ∑ ρ ∈ S_off, zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log T) (zetaDepth ρ)
        ≤ ∑ ρ ∈ S_off, (zetaZeroConfig.mult ρ : ℝ) * ((2 ^ K * C_K) ^ 2 / T ^ N) :=
          Finset.sum_le_sum hterm
      _ = (M_mult * (2 ^ K * C_K) ^ 2) / T ^ N := by rw [← Finset.sum_mul, mul_div_assoc]
      _ ≤ C_high / T ^ N :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) hTN_pos.le
      _ ≤ (C_low + C_high + 1) / T ^ N :=
          div_le_div_of_nonneg_right (by linarith) hTN_pos.le

/-- Corollary: Under `FiniteOffLine`, `T ^ N * ∫_{T}^{T+1} E_γ(c log T) dγ → 0` for every `c > 0`
and every `N : ℕ`. -/
theorem tendsto_pow_mul_unitWindow_heckeDefect_of_finiteOffLine (hF : FiniteOffLine)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun T : ℝ =>
      T ^ N * ∫ γ in Icc T (T + 1), heckeDefect (baseTwistTest γ) (c * Real.log T))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := exists_heckeDefect_log_le_div_pow_of_finiteOffLine hF hc (N + 1)
  have htend : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    refine mul_nonneg (pow_nonneg (by linarith) N) ?_
    exact setIntegral_nonneg measurableSet_Icc fun γ _ => heckeDefect_nonneg _ _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    have hT_pos : 0 < T := by linarith
    have hint := integrableOn_heckeDefect_Icc T (T + 1) (c * Real.log T)
    have hint_c : IntegrableOn (fun _ : ℝ => C / T ^ (N + 1)) (Icc T (T + 1)) volume :=
      integrableOn_const (by simp)
    have hmono := setIntegral_mono_on hint hint_c measurableSet_Icc
      (fun γ hγ => hbd T hT γ hγ)
    have hvol : volume.real (Icc T (T + 1)) = 1 := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    rw [setIntegral_const, hvol, one_smul] at hmono
    calc T ^ N * ∫ γ in Icc T (T + 1), heckeDefect (baseTwistTest γ) (c * Real.log T)
        ≤ T ^ N * (C / T ^ (N + 1)) := mul_le_mul_of_nonneg_left hmono (pow_nonneg hT_pos.le N)
      _ = C / T := by rw [pow_succ]; field_simp

/-- **Theorem 2b (`exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine`).**
Under `FiniteOffLine`, for EVERY `c > 0`, `α ≥ 0`, and EVERY prime cutoff `M : ℝ → ℕ` (including
both `M T = ⌊T ^ (2 * c)⌋₊` and `M T = ⌊exp(2(c log T + 1/4))⌋₊`), there exists `C > 0` such that
for all `T ≥ 2` and all `γ ∈ [T, T + 1)`,
`heckeDefect (baseTwistTest γ) (c * log T) ≤ α * ‖primePolynomial (heckeAvgBump (c * log T)) (M T) (-γ / 2π)‖ + C`. -/
theorem exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine (hF : FiniteOffLine)
    {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 ≤ α) (M : ℝ → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
        α * ‖primePolynomial (heckeAvgBump (c * Real.log T)) (M T) (-γ / (2 * Real.pi))‖ + C := by
  obtain ⟨C, hC, hbd⟩ := exists_heckeDefect_log_le_div_pow_of_finiteOffLine hF hc 0
  refine ⟨C, hC, fun T hT γ hγ => ?_⟩
  have h1 := hbd T hT γ hγ
  rw [pow_zero, div_one] at h1
  exact h1.trans (le_add_of_nonneg_left (mul_nonneg hα (norm_nonneg _)))

/-- Helper lower bound on `-(primePolynomial (heckeAvgBump L) N*(L) (-γ / 2π)).re` whenever
`heckeDefect (baseTwistTest γ) (c * log T) ≤ B` and `1 ≤ c * log T`. -/
theorem neg_re_primePolynomial_ge_of_heckeDefect_le {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ C_neg : ℝ, 0 < C_neg ∧ ∀ T γ : ℝ, 2 ≤ T → 1 ≤ c * Real.log T →
      T ≤ γ → γ ≤ T + 1 → heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ B →
      -C_neg ≤ -(primePolynomial (heckeAvgBump (c * Real.log T))
        ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re := by
  obtain ⟨C_arch, hCarch, harch_bd⟩ := exists_abs_re_archPart_heckeAvgBump_log_le hc
  have hsinc_pos := sincLorentzConst_pos
  set C_neg : ℝ := C_arch + 4 * B + sincLorentzConst * (1 + 4 / c) + 1
  refine ⟨C_neg, by positivity, fun T γ hT2 hL1 hγT hγT1 hEB => ?_⟩
  set L : ℝ := c * Real.log T
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  set ξ : ℝ := -γ / (2 * Real.pi)
  have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
    (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hLpos) ξ
  have htw : twist γ (heckeAvgBump L) = heightShift ξ (heckeAvgBump L) := twist_eq_heightShift γ _
  have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
    (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
  have hcap := re_W_eq_collided_sub_defect (Z := zetaZeroConfig) hs
  rw [htw] at hcap
  have hcoll_nn : 0 ≤ collidedForm zetaZeroConfig (heightShift ξ (heckeAvgBump L)) :=
    tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have harch := (abs_le.mp (harch_bd T γ hT2 hL1 hγT hγT1)).2
  have hdef := offLineDefect_heckeAvg_le_heckeDefect_add_lorentz hLpos γ
  rw [htw] at hdef
  have hlog_tail : sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 ≤
      sincLorentzConst * (1 + 4 / c) := by
    have habsγ : |γ| = γ := abs_of_pos (by linarith)
    rw [habsγ]
    have hT0 : 0 ≤ T := by linarith
    have hγ4 : γ + 4 ≤ T ^ 4 := by
      have : 0 ≤ (T - 2) * (T ^ 3 + 2 * T ^ 2 + 4 * T + 7) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    have hlog4 : Real.log (γ + 4) ≤ 4 * Real.log T := by
      calc Real.log (γ + 4) ≤ Real.log (T ^ 4) := Real.log_le_log (by linarith) hγ4
        _ = 4 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have h1 : sincLorentzConst * (1 + Real.log (γ + 4)) / L ^ 2 ≤
        sincLorentzConst * (1 + 4 * Real.log T) / L := by
      calc sincLorentzConst * (1 + Real.log (γ + 4)) / L ^ 2
          ≤ sincLorentzConst * (1 + 4 * Real.log T) / L ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hsinc_pos.le)
              (sq_nonneg _)
        _ ≤ sincLorentzConst * (1 + 4 * Real.log T) / L :=
            div_le_div_of_nonneg_left
              (mul_nonneg hsinc_pos.le (by linarith [Real.log_nonneg (by linarith : 1 ≤ T)]))
              hLpos hLsq
    have hlogT_ne : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
    have h2 : sincLorentzConst * (1 + 4 * Real.log T) / L ≤ sincLorentzConst * (1 + 4 / c) := by
      have hsplit : sincLorentzConst * (1 + 4 * Real.log T) / L =
          sincLorentzConst / L + sincLorentzConst * ((4 * Real.log T) / (c * Real.log T)) := by
        dsimp [L]; ring
      rw [hsplit]
      have hdiv1 : sincLorentzConst / L ≤ sincLorentzConst := div_le_self hsinc_pos.le hL1
      have hdiv2 : (4 * Real.log T) / (c * Real.log T) = 4 / c := by field_simp
      rw [hdiv2]; linarith
    exact h1.trans h2
  dsimp [C_neg]
  linarith

/-- **Theorem 2c (`exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine`).**
Under `FiniteOffLine`, for EVERY `c > 0` and `α ≥ 0`, the signed prime-polynomial bound
`heckeDefect (baseTwistTest γ) (c * log T) ≤ -α * (primePolynomial (heckeAvgBump (c * log T)) N*(c * log T) (-γ / 2π)).re + C'`
also holds globally for all `T ≥ 2` and `γ ∈ [T, T + 1)`. -/
theorem exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine (hF : FiniteOffLine)
    {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ T : ℝ, 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
        -α * (primePolynomial (heckeAvgBump (c * Real.log T))
          ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re + C' := by
  obtain ⟨C₀, hC₀, hbd0⟩ := exists_heckeDefect_log_le_div_pow_of_finiteOffLine hF hc 0
  obtain ⟨C_neg, hCneg, hneg_hi⟩ := neg_re_primePolynomial_ge_of_heckeDefect_le hc hC₀.le
  set T_hi : ℝ := max 2 (Real.exp (1 / c))
  set C_env : ℝ := 2 * Real.exp (2 * (c * Real.log T_hi + 1 / 4)) / (c * Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hCenv_pos : 0 < C_env := by dsimp [C_env]; positivity
  refine ⟨C₀ + α * (C_neg + C_env) + 1, by positivity, fun T hT2 γ hγ => ?_⟩
  have hE : heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ C₀ := by
    have := hbd0 T hT2 γ hγ
    rwa [pow_zero, div_one] at this
  rcases le_or_gt (1 : ℝ) (c * Real.log T) with hL1 | hL_lt1
  · have hneg := hneg_hi T γ hT2 hL1 hγ.1 hγ.2 hE
    have hα_neg : -α * C_neg ≤ -α * (primePolynomial (heckeAvgBump (c * Real.log T))
        ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re := by
      have := mul_le_mul_of_nonneg_left hneg hα
      linarith
    have : 0 ≤ α * C_env := mul_nonneg hα hCenv_pos.le
    linarith
  · -- `2 ≤ T` with `c * log T < 1`: `T ≤ exp(1 / c) ≤ T_hi`, bound via `primeEnvelope_heckeAvgBump_le`
    set L : ℝ := c * Real.log T
    have hL_ge : c * Real.log 2 ≤ L :=
      mul_le_mul_of_nonneg_left (Real.log_le_log zero_lt_two hT2) hc.le
    have hLpos : 0 < L := lt_of_lt_of_le (mul_pos hc hlog2_pos) hL_ge
    have hT_le_hi : T ≤ T_hi := by
      have hlog_lt : Real.log T < 1 / c := (lt_div_iff₀' hc).mpr hL_lt1
      have hexp : T ≤ Real.exp (1 / c) := by
        rw [← Real.exp_log (by linarith : 0 < T)]
        exact Real.exp_le_exp.mpr hlog_lt.le
      exact hexp.trans (le_max_right _ _)
    set N_cut : ℕ := ⌊Real.exp (2 * (L + 1 / 4))⌋₊
    have hre_le : (primePolynomial (heckeAvgBump L) N_cut (-γ / (2 * Real.pi))).re ≤ C_env := by
      have h1 := re_primePolynomial_le_primeEnvelope (heckeAvgBump L) N_cut (-γ / (2 * Real.pi))
      have h2 := primeEnvelope_heckeAvgBump_le hLpos N_cut
      have hN_le : (N_cut : ℝ) ≤ Real.exp (2 * (c * Real.log T_hi + 1 / 4)) := by
        refine (Nat.floor_le (Real.exp_pos _).le).trans ?_
        refine Real.exp_le_exp.mpr ?_
        have hlog_mono : Real.log T ≤ Real.log T_hi := Real.log_le_log (by linarith) hT_le_hi
        dsimp [L]; nlinarith
      calc (primePolynomial (heckeAvgBump L) N_cut (-γ / (2 * Real.pi))).re
          ≤ 2 * (N_cut : ℝ) / L := h1.trans h2
        _ ≤ 2 * Real.exp (2 * (c * Real.log T_hi + 1 / 4)) / L :=
            div_le_div_of_nonneg_right (by linarith) hLpos.le
        _ ≤ 2 * Real.exp (2 * (c * Real.log T_hi + 1 / 4)) / (c * Real.log 2) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hc hlog2_pos) hL_ge
    have hα_env : -α * C_env ≤ -α * (primePolynomial (heckeAvgBump L) N_cut (-γ / (2 * Real.pi))).re := by
      have := mul_le_mul_of_nonneg_left hre_le hα
      linarith
    have : 0 ≤ α * C_neg := mul_nonneg hα hCneg.le
    linarith

/-! ## §3. Theorem 3 — All-`c` scale transfer, 5-way TFAE, and positive-sign separation -/

/-- **Theorem 3a (`unitWindowDepthCharge_log_iff_of_pos` — All-`c` Scale Transfer).**
Boundedness of `unitWindowDepthCharge T (c * log T)` eventually in `T` is invariant under changing
`c > 0` to any other `c' > 0`. -/
theorem unitWindowDepthCharge_log_iff_of_pos {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (c₁ * Real.log T) ≤ B) ↔
      (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (c₂ * Real.log T) ≤ B) := by
  suffices ∀ {a b : ℝ}, 0 < a → 0 < b →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (a * Real.log T) ≤ B) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (b * Real.log T) ≤ B) from
    ⟨this hc₁ hc₂, this hc₂ hc₁⟩
  intro a b ha hb ⟨B, hB, hev⟩
  obtain ⟨K, hK1, htr⟩ := exists_depthKernel_scale_transfer B (b / a) hB
  refine ⟨K * B, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with T hTB hT2
  have hlog_nn : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hterm : ∀ ρ ∈ xiUnitWindowZeros T,
      ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel (b * Real.log T) (ρ.re - 1 / 2) ≤
        K * (((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel (a * Real.log T) (ρ.re - 1 / 2)) := by
    intro ρ hρ
    have hdk_B : depthKernel (a * Real.log T) (ρ.re - 1 / 2) ≤ B :=
      (depthKernel_le_unitWindowDepthCharge hρ).trans hTB
    have hscale : b * Real.log T ≤ (b / a) * (a * Real.log T) := by
      have ha_ne : a ≠ 0 := ha.ne'
      exact le_of_eq (by field_simp)
    have hdk_tr := htr (a * Real.log T) (b * Real.log T) (ρ.re - 1 / 2)
      (mul_nonneg ha.le hlog_nn) (mul_nonneg hb.le hlog_nn) hscale hdk_B
    calc ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel (b * Real.log T) (ρ.re - 1 / 2)
        ≤ ((analyticOrderAt xi ρ).toNat : ℝ) * (K * depthKernel (a * Real.log T) (ρ.re - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hdk_tr (Nat.cast_nonneg _)
      _ = K * (((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel (a * Real.log T) (ρ.re - 1 / 2)) := by
          ring
  calc unitWindowDepthCharge T (b * Real.log T)
      ≤ ∑ ρ ∈ xiUnitWindowZeros T,
          K * (((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel (a * Real.log T) (ρ.re - 1 / 2)) :=
        Finset.sum_le_sum hterm
    _ = K * unitWindowDepthCharge T (a * Real.log T) := by rw [← Finset.mul_sum]; rfl
    _ ≤ K * B := mul_le_mul_of_nonneg_left hTB (by linarith)

/-- Core reconstruction `(v) → (iii)`: an eventual uniform bound on `unitWindowDepthCharge T (c * log T)`
upgrades via dyadic scale transfer (`L = c log T ≤ 2 c log(T/2 + m)`) and `baseBump` Paley–Wiener
summability to a uniform bound on the full infinite series `heckeDefect (baseTwistTest γ) (c * log T)`. -/
theorem eventually_heckeDefect_le_of_unitWindowDepthCharge_le {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hev : ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (c * Real.log T) ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ B' := by
  classical
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (4 : ℝ)))
  obtain ⟨K₂, hK₂1, htr2⟩ := exists_depthKernel_scale_transfer B 2 hB
  set K_pw : ℕ := ⌈c⌉₊ + 2
  obtain ⟨C_pw, hCpw, hpw_low⟩ := exists_norm_tr_twist_baseBump_le_pow K_pw
  obtain ⟨C₁, hC₁, hpw1⟩ := exists_norm_tr_twist_baseBump_le_pow 1
  obtain ⟨_, _, hlor⟩ := exists_zetaZeroConfig_lorentz_le
  have hlor0_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using (hlor 0).1
  set M_lor0 : ℝ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))
  have hMlor0_nn : 0 ≤ M_lor0 :=
    tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hinv_sq_sum : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := by
    simpa only [one_div] using Real.summable_nat_pow_inv.mpr one_lt_two
  set S_zeta2 : ℝ := ∑' k : ℕ, 1 / (k : ℝ) ^ 2
  have hS2_nn : 0 ≤ S_zeta2 := tsum_nonneg fun _ => by positivity
  set B_low : ℝ := 16 * C_pw ^ 2 * M_lor0
  set B_high : ℝ := 3 * Real.exp (1 / 4) * K₂ * B + 2 * C₁ ^ 2 * K₂ * B * S_zeta2
  refine ⟨B_low + B_high, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (2 * T₀ + 16) 16)] with T hT γ hγ
  have hT_ge16 : 16 ≤ T := (le_max_right _ _).trans hT
  have hT_ge2T₀ : 2 * T₀ + 16 ≤ T := (le_max_left _ _).trans hT
  have hT_pos : 0 < T := by linarith
  set L : ℝ := c * Real.log T
  have hL_nn : 0 ≤ L := mul_nonneg hc.le (Real.log_nonneg (by linarith))
  -- Apply `Real.tsum_le_of_sum_le` on arbitrary finite subsets `F : Finset zetaZeroConfig.carrier`
  refine Real.tsum_le_of_sum_le
    (fun ρ => mul_nonneg (zetaWeight_nonneg _ _) (depthKernel_nonneg _ _)) (fun F => ?_)
  set F_low := F.filter (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im < T / 2)
  set F_high := F.filter (fun ρ : zetaZeroConfig.carrier => ¬ (ρ : ℂ).im < T / 2)
  have hsplit : (∑ ρ ∈ F, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)) =
      (∑ ρ ∈ F_low, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)) +
        ∑ ρ ∈ F_high, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) :=
    (Finset.sum_filter_add_sum_filter_not F _ _).symm
  rw [hsplit]
  -- Part A: Low-ordinate sum `F_low` (`Im ρ < T / 2`)
  have hlow_le : ∑ ρ ∈ F_low, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ≤ B_low := by
    have hterm_low : ∀ ρ ∈ F_low,
        zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ≤
          16 * C_pw ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by
      intro ρ hρ
      have him_lt : (ρ : ℂ).im < T / 2 := (Finset.mem_filter.mp hρ).2
      have hsep_T : T / 2 ≤ |(ρ : ℂ).im - γ| := by
        rw [abs_sub_comm]
        exact (by linarith [hγ.1] : T / 2 ≤ γ - (ρ : ℂ).im).trans (le_abs_self _)
      have hsep_im : (1 + |(ρ : ℂ).im|) / 4 ≤ |(ρ : ℂ).im - γ| := by
        rw [abs_sub_comm]
        refine (?_ : (1 + |(ρ : ℂ).im|) / 4 ≤ γ - (ρ : ℂ).im).trans (le_abs_self _)
        rcases le_or_gt 0 (ρ : ℂ).im with him0 | him_neg
        · rw [abs_of_nonneg him0]; linarith [hγ.1]
        · rw [abs_of_neg him_neg]; linarith [hγ.1]
      have hne : (ρ : ℂ).im ≠ γ := by
        intro heq; rw [heq, sub_self, abs_zero] at hsep_T; linarith
      have hpw_ρ := hpw_low γ ρ (abs_zetaDepth_le ρ) hne
      have hnsq : Complex.normSq (tr (twist γ baseBump) ρ) ≤
          C_pw ^ 2 / |(ρ : ℂ).im - γ| ^ (2 * K_pw) := by
        rw [Complex.normSq_eq_norm_sq]
        refine (pow_le_pow_left₀ (norm_nonneg _) hpw_ρ 2).trans_eq ?_
        rw [div_pow, ← pow_mul, mul_comm K_pw 2]
      have hdk : depthKernel L (zetaDepth ρ) ≤ T ^ ⌈c⌉₊ := by
        refine (depthKernel_le_exp_of_abs_le_half hL_nn (abs_zetaDepth_le ρ)).trans ?_
        calc Real.exp (c * Real.log T)
            ≤ Real.exp ((⌈c⌉₊ : ℝ) * Real.log T) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (Real.log_nonneg (by linarith)))
          _ = T ^ ⌈c⌉₊ := by rw [Real.exp_nat_mul, Real.exp_log hT_pos]
      -- Lower bound `|ρ.im - γ| ^ (2 * K_pw) ≥ T ^ ⌈c⌉₊ * ((1 + im^2) / 16)`
      have hden_ge : T ^ ⌈c⌉₊ * ((1 + (ρ : ℂ).im ^ 2) / 16) ≤ |(ρ : ℂ).im - γ| ^ (2 * K_pw) := by
        have h2K : 2 * K_pw = 2 * ⌈c⌉₊ + 2 + 2 := by dsimp [K_pw]; omega
        rw [h2K, pow_add, pow_add]
        have hT_sq : T ≤ (T / 2) ^ 2 := by nlinarith
        have hpart1 : T ^ ⌈c⌉₊ ≤ |(ρ : ℂ).im - γ| ^ (2 * ⌈c⌉₊) := by
          calc T ^ ⌈c⌉₊ ≤ ((T / 2) ^ 2) ^ ⌈c⌉₊ := pow_le_pow_left₀ hT_pos.le hT_sq ⌈c⌉₊
            _ ≤ (|(ρ : ℂ).im - γ| ^ 2) ^ ⌈c⌉₊ :=
                pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hsep_T 2) ⌈c⌉₊
            _ = |(ρ : ℂ).im - γ| ^ (2 * ⌈c⌉₊) := (pow_mul _ 2 ⌈c⌉₊).symm
        have h1_le_sq : 1 ≤ |(ρ : ℂ).im - γ| ^ 2 := by
          have : 1 ≤ T / 2 := by linarith
          nlinarith [this.trans hsep_T]
        have hpart2 : (1 + (ρ : ℂ).im ^ 2) / 16 ≤ |(ρ : ℂ).im - γ| ^ 2 := by
          have hsq1 : ((1 + |(ρ : ℂ).im|) / 4) ^ 2 ≤ |(ρ : ℂ).im - γ| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hsep_im 2
          have hsq2 : (1 + (ρ : ℂ).im ^ 2) / 16 ≤ ((1 + |(ρ : ℂ).im|) / 4) ^ 2 := by
            have : (ρ : ℂ).im ^ 2 = |(ρ : ℂ).im| ^ 2 := (sq_abs _).symm
            rw [this]; nlinarith [abs_nonneg (ρ : ℂ).im]
          exact hsq2.trans hsq1
        calc T ^ ⌈c⌉₊ * ((1 + (ρ : ℂ).im ^ 2) / 16)
            = (T ^ ⌈c⌉₊ * 1) * ((1 + (ρ : ℂ).im ^ 2) / 16) := by ring
          _ ≤ (|(ρ : ℂ).im - γ| ^ (2 * ⌈c⌉₊) * |(ρ : ℂ).im - γ| ^ 2) * |(ρ : ℂ).im - γ| ^ 2 := by
              refine mul_le_mul (mul_le_mul hpart1 h1_le_sq zero_le_one (by positivity))
                hpart2 (by positivity) (by positivity)
      have hprod_le : Complex.normSq (tr (twist γ baseBump) ρ) * depthKernel L (zetaDepth ρ) ≤
          16 * C_pw ^ 2 * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
        have hden_pos : 0 < T ^ ⌈c⌉₊ * ((1 + (ρ : ℂ).im ^ 2) / 16) := by positivity
        calc Complex.normSq (tr (twist γ baseBump) ρ) * depthKernel L (zetaDepth ρ)
            ≤ (C_pw ^ 2 / |(ρ : ℂ).im - γ| ^ (2 * K_pw)) * T ^ ⌈c⌉₊ :=
              mul_le_mul hnsq hdk (depthKernel_nonneg _ _) (by positivity)
          _ ≤ (C_pw ^ 2 / (T ^ ⌈c⌉₊ * ((1 + (ρ : ℂ).im ^ 2) / 16))) * T ^ ⌈c⌉₊ :=
              mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_left (sq_nonneg _) hden_pos hden_ge) (by positivity)
          _ = 16 * C_pw ^ 2 * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
              have hTc_ne : (T : ℝ) ^ ⌈c⌉₊ ≠ 0 := (pow_pos hT_pos ⌈c⌉₊).ne'
              have h1im_ne : 1 + (ρ : ℂ).im ^ 2 ≠ 0 := by positivity
              field_simp
      dsimp [zetaWeight, baseTwistTest]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
            depthKernel L (zetaDepth ρ)
          = (zetaZeroConfig.mult ρ : ℝ) *
              (Complex.normSq (tr (twist γ baseBump) ρ) * depthKernel L (zetaDepth ρ)) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (16 * C_pw ^ 2 * (1 / (1 + (ρ : ℂ).im ^ 2))) :=
            mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg _)
        _ = 16 * C_pw ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by ring
    calc ∑ ρ ∈ F_low, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)
        ≤ ∑ ρ ∈ F_low, 16 * C_pw ^ 2 *
            ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) :=
          Finset.sum_le_sum hterm_low
      _ = 16 * C_pw ^ 2 * ∑ ρ ∈ F_low,
            (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
          rw [← Finset.mul_sum]
      _ ≤ 16 * C_pw ^ 2 * M_lor0 :=
          mul_le_mul_of_nonneg_left
            (hlor0_sum.sum_le_tsum F_low fun _ _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
            (by positivity)
  -- Part B: High-ordinate sum `F_high` (`Im ρ ≥ T / 2`), fibred by `m(ρ) = ⌊Im ρ - T / 2⌋₊`
  have hhigh_le : ∑ ρ ∈ F_high, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ≤ B_high := by
    let idx : zetaZeroConfig.carrier → ℕ := fun ρ => ⌊(ρ : ℂ).im - T / 2⌋₊
    set M_F : ℕ := F_high.sup idx + 1
    have hmaps : ∀ ρ ∈ F_high, idx ρ ∈ Finset.range M_F := fun ρ hρ =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hρ))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    -- Fibre depth-charge bound: for every `m : ℕ`,
    -- `∑ ρ ∈ F_high with idx ρ = m, mult ρ * depthKernel L (zetaDepth ρ) ≤ K₂ * B`
    have hfibre_depth : ∀ m : ℕ,
        (∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
          (zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) ≤ K₂ * B := by
      intro m
      set U_m : ℝ := T / 2 + (m : ℝ)
      have hUm_ge_T₀ : T₀ ≤ U_m := by dsimp [U_m]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hUm_ge8 : 8 ≤ U_m := by dsimp [U_m]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hUm_B : unitWindowDepthCharge U_m (c * Real.log U_m) ≤ B := (hT₀ U_m hUm_ge_T₀).1
      have hL_le_2Lm : L ≤ 2 * (c * Real.log U_m) := by
        have hT_le_sq : T ≤ U_m ^ 2 := by
          have : (T / 2) ^ 2 ≤ U_m ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by dsimp [U_m]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) 2
          nlinarith
        have hlog_le : Real.log T ≤ 2 * Real.log U_m := by
          calc Real.log T ≤ Real.log (U_m ^ 2) := Real.log_le_log hT_pos hT_le_sq
            _ = 2 * Real.log U_m := by rw [Real.log_pow]; push_cast; rfl
        dsimp [L]; nlinarith
      -- Every `ρ ∈ F_high` with `idx ρ = m` maps injectively into `xiUnitWindowZeros U_m`
      have hmem_W : ∀ ρ ∈ F_high.filter (fun ρ => idx ρ = m), (ρ : ℂ) ∈ xiUnitWindowZeros U_m := by
        intro ρ hρ
        obtain ⟨hρ_hi, hm_eq⟩ := Finset.mem_filter.mp hρ
        have him_ge : T / 2 ≤ (ρ : ℂ).im := not_lt.mp (Finset.mem_filter.mp hρ_hi).2
        have hsub_nn : 0 ≤ (ρ : ℂ).im - T / 2 := by linarith
        have hm_le : (m : ℝ) ≤ (ρ : ℂ).im - T / 2 := by
          rw [← hm_eq]; exact Nat.floor_le hsub_nn
        have hm_lt : (ρ : ℂ).im - T / 2 < (m : ℝ) + 1 := by
          rw [← hm_eq]; exact Nat.lt_floor_add_one _
        obtain ⟨hxi, h0, h1⟩ :=
          CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp ρ.2
        rw [mem_xiUnitWindowZeros]
        refine ⟨(Set.Finite.mem_toFinset _).mpr ⟨⟨h0, h1, by linarith, by dsimp [U_m]; linarith⟩, hxi⟩,
          by dsimp [U_m]; linarith⟩
      have hval_inj : Set.InjOn (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ))
          (F_high.filter (fun ρ => idx ρ = m) : Set zetaZeroConfig.carrier) :=
        fun _ _ _ _ h => Subtype.ext h
      have himg_sub : (F_high.filter (fun ρ => idx ρ = m)).image (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) ⊆
          xiUnitWindowZeros U_m := by
        intro z hz
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
        exact hmem_W ρ hρ
      have hterm_m : ∀ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
          (zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ) ≤
            K₂ * (((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) *
              depthKernel (c * Real.log U_m) ((ρ : ℂ).re - 1 / 2)) := by
        intro ρ hρ
        have hzW := hmem_W ρ hρ
        obtain ⟨_, h0, h1⟩ :=
          CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp ρ.2
        have hmult : zetaZeroConfig.mult (ρ : ℂ) = (analyticOrderAt xi (ρ : ℂ)).toNat :=
          (congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩)).symm
        have hdk_B : depthKernel (c * Real.log U_m) ((ρ : ℂ).re - 1 / 2) ≤ B :=
          (depthKernel_le_unitWindowDepthCharge hzW).trans hUm_B
        have hdk_tr := htr2 (c * Real.log U_m) L ((ρ : ℂ).re - 1 / 2)
          (mul_nonneg hc.le (Real.log_nonneg (by linarith))) hL_nn hL_le_2Lm hdk_B
        rw [hmult]
        dsimp [zetaDepth]
        calc ((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)
            ≤ ((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) *
                (K₂ * depthKernel (c * Real.log U_m) ((ρ : ℂ).re - 1 / 2)) :=
              mul_le_mul_of_nonneg_left hdk_tr (Nat.cast_nonneg _)
          _ = K₂ * (((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) *
                depthKernel (c * Real.log U_m) ((ρ : ℂ).re - 1 / 2)) := by ring
      calc ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
            (zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)
          ≤ ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
              K₂ * (((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) *
                depthKernel (c * Real.log U_m) ((ρ : ℂ).re - 1 / 2)) :=
            Finset.sum_le_sum hterm_m
        _ = K₂ * ∑ z ∈ (F_high.filter (fun ρ => idx ρ = m)).image (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)),
              ((analyticOrderAt xi z).toNat : ℝ) * depthKernel (c * Real.log U_m) (z.re - 1 / 2) := by
            rw [Finset.sum_image hval_inj, ← Finset.mul_sum]
        _ ≤ K₂ * unitWindowDepthCharge U_m (c * Real.log U_m) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg himg_sub
                fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _))
              (by linarith)
        _ ≤ K₂ * B := mul_le_mul_of_nonneg_left hUm_B (by linarith)
    -- Split `m ∈ Finset.range M_F` around `N_γ = ⌊γ - T / 2⌋₊ ≥ 8`
    set N_γ : ℕ := ⌊γ - T / 2⌋₊
    have hγ_sub_nn : 0 ≤ γ - T / 2 := by linarith [hγ.1]
    have hNγ_le : (N_γ : ℝ) ≤ γ - T / 2 := Nat.floor_le hγ_sub_nn
    have hNγ_lt : γ - T / 2 < (N_γ : ℝ) + 1 := Nat.lt_floor_add_one _
    let fibSum : ℕ → ℝ := fun m =>
      ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
        zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)
    have hfib_nn : ∀ m, 0 ≤ fibSum m := fun m =>
      Finset.sum_nonneg fun _ _ => mul_nonneg (zetaWeight_nonneg _ _) (depthKernel_nonneg _ _)
    -- Bound on any single fibre (`≤ exp(1/4) * K₂ * B`)
    have hfib_near : ∀ m : ℕ, fibSum m ≤ Real.exp (1 / 4) * K₂ * B := by
      intro m
      have hb_term : ∀ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
          zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ≤
            Real.exp (1 / 4) * ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) := by
        intro ρ _
        have hb : Complex.normSq (tr (twist γ baseBump) ρ) ≤ Real.exp (1 / 4) := by
          rw [Complex.normSq_eq_norm_sq]
          refine (pow_le_pow_left₀ (norm_nonneg _)
            (norm_tr_twist_baseBump_le_exp γ (abs_zetaDepth_le ρ)) 2).trans_eq ?_
          rw [← Real.exp_nat_mul]; norm_num
        dsimp [zetaWeight, baseTwistTest]
        calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L (zetaDepth ρ)
            = Complex.normSq (tr (twist γ baseBump) ρ) *
                ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) := by ring
          _ ≤ Real.exp (1 / 4) * ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) :=
              mul_le_mul_of_nonneg_right hb
                (mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _))
      calc fibSum m
          ≤ ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
              Real.exp (1 / 4) * ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) :=
            Finset.sum_le_sum hb_term
        _ = Real.exp (1 / 4) * ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
              (zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ) := by
            rw [← Finset.mul_sum]
        _ ≤ Real.exp (1 / 4) * (K₂ * B) :=
            mul_le_mul_of_nonneg_left (hfibre_depth m) (Real.exp_pos _).le
        _ = Real.exp (1 / 4) * K₂ * B := by ring
    -- Bound on separated fibre (`dist ≥ d ≥ 1` gives `≤ C₁^2 * K₂ * B * (1 / d^2)`)
    have hfib_sep : ∀ m d : ℕ, 1 ≤ d →
        (∀ ρ ∈ F_high.filter (fun ρ => idx ρ = m), (d : ℝ) ≤ |(ρ : ℂ).im - γ|) →
        fibSum m ≤ C₁ ^ 2 * K₂ * B * (1 / (d : ℝ) ^ 2) := by
      intro m d hd1 hsep_d
      have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd1
      have hterm_s : ∀ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
          zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ≤
            (C₁ ^ 2 * (1 / (d : ℝ) ^ 2)) *
              ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) := by
        intro ρ hρ
        have hsep := hsep_d ρ hρ
        have hne : (ρ : ℂ).im ≠ γ := by
          intro heq; rw [heq, sub_self, abs_zero] at hsep; linarith
        have hpw_ρ := hpw1 γ ρ (abs_zetaDepth_le ρ) hne
        rw [pow_one] at hpw_ρ
        have hnorm_le : ‖tr (twist γ baseBump) ρ‖ ≤ C₁ / (d : ℝ) :=
          hpw_ρ.trans (div_le_div_of_nonneg_left hC₁.le hd_pos hsep)
        have hnsq_le : Complex.normSq (tr (twist γ baseBump) ρ) ≤ C₁ ^ 2 * (1 / (d : ℝ) ^ 2) := by
          rw [Complex.normSq_eq_norm_sq]
          refine (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2).trans_eq ?_
          rw [div_pow]; ring
        dsimp [zetaWeight, baseTwistTest]
        calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L (zetaDepth ρ)
            = Complex.normSq (tr (twist γ baseBump) ρ) *
                ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) := by ring
          _ ≤ (C₁ ^ 2 * (1 / (d : ℝ) ^ 2)) *
                ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) :=
              mul_le_mul_of_nonneg_right hnsq_le
                (mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _))
      calc fibSum m
          ≤ ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
              (C₁ ^ 2 * (1 / (d : ℝ) ^ 2)) *
                ((zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ)) :=
            Finset.sum_le_sum hterm_s
        _ = (C₁ ^ 2 * (1 / (d : ℝ) ^ 2)) * ∑ ρ ∈ F_high.filter (fun ρ => idx ρ = m),
              (zetaZeroConfig.mult ρ : ℝ) * depthKernel L (zetaDepth ρ) := by
            rw [← Finset.mul_sum]
        _ ≤ (C₁ ^ 2 * (1 / (d : ℝ) ^ 2)) * (K₂ * B) :=
            mul_le_mul_of_nonneg_left (hfibre_depth m) (by positivity)
        _ = C₁ ^ 2 * K₂ * B * (1 / (d : ℝ) ^ 2) := by ring
    -- Partition `Finset.range M_F` into left tail `m + 2 ≤ N_γ`, near `{N_γ - 1, N_γ, N_γ + 1}`,
    -- and right tail `N_γ + 2 ≤ m`
    set R_left := (Finset.range M_F).filter (fun m => m + 2 ≤ N_γ)
    set R_mid := (Finset.range M_F).filter (fun m => ¬ m + 2 ≤ N_γ ∧ m ≤ N_γ + 1)
    set R_right := (Finset.range M_F).filter (fun m => ¬ m + 2 ≤ N_γ ∧ ¬ m ≤ N_γ + 1)
    have hpart_sum : ∑ m ∈ Finset.range M_F, fibSum m =
        ∑ m ∈ R_left, fibSum m + (∑ m ∈ R_mid, fibSum m + ∑ m ∈ R_right, fibSum m) := by
      have h1 := (Finset.sum_filter_add_sum_filter_not (Finset.range M_F)
        (fun m => m + 2 ≤ N_γ) fibSum).symm
      have h2 := (Finset.sum_filter_add_sum_filter_not
        ((Finset.range M_F).filter (fun m => ¬ m + 2 ≤ N_γ))
        (fun m => m ≤ N_γ + 1) fibSum).symm
      rw [Finset.filter_filter, Finset.filter_filter] at h2
      rw [h1, h2]
    change ∑ m ∈ Finset.range M_F, fibSum m ≤ B_high
    rw [hpart_sum]
    -- Near sum `R_mid ⊆ {N_γ - 1, N_γ, N_γ + 1}` (`≤ 3` fibres)
    have hmid_le : ∑ m ∈ R_mid, fibSum m ≤ 3 * Real.exp (1 / 4) * K₂ * B := by
      have hsub_mid : R_mid ⊆ {N_γ - 1, N_γ, N_γ + 1} := by
        intro m hm
        obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hm
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      calc ∑ m ∈ R_mid, fibSum m
          ≤ ∑ m ∈ ({N_γ - 1, N_γ, N_γ + 1} : Finset ℕ), fibSum m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_mid fun _ _ _ => hfib_nn _
        _ ≤ ∑ _m ∈ ({N_γ - 1, N_γ, N_γ + 1} : Finset ℕ), (Real.exp (1 / 4) * K₂ * B) :=
            Finset.sum_le_sum fun m _ => hfib_near m
        _ = (({N_γ - 1, N_γ, N_γ + 1} : Finset ℕ).card : ℝ) * (Real.exp (1 / 4) * K₂ * B) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (Real.exp (1 / 4) * K₂ * B) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hcard : ({N_γ - 1, N_γ, N_γ + 1} : Finset ℕ).card ≤ 3 := by
              exact (Finset.card_insert_le _ _).trans
                (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
            exact_mod_cast hcard
        _ = 3 * Real.exp (1 / 4) * K₂ * B := by ring
    -- Left tail `R_left`: map `m ↦ N_γ - 1 - m ≥ 1` injectively into `ℕ`
    have hleft_le : ∑ m ∈ R_left, fibSum m ≤ C₁ ^ 2 * K₂ * B * S_zeta2 := by
      let φ_L : ℕ → ℕ := fun m => N_γ - 1 - m
      have hinj_L : Set.InjOn φ_L (R_left : Set ℕ) := by
        intro a ha b hb hab
        have ha' : a + 2 ≤ N_γ := (Finset.mem_filter.mp ha).2
        have hb' : b + 2 ≤ N_γ := (Finset.mem_filter.mp hb).2
        dsimp [φ_L] at hab; omega
      have hterm_L : ∀ m ∈ R_left, fibSum m ≤ C₁ ^ 2 * K₂ * B * (1 / (φ_L m : ℝ) ^ 2) := by
        intro m hm
        have hm' : m + 2 ≤ N_γ := (Finset.mem_filter.mp hm).2
        refine hfib_sep m (φ_L m) (by dsimp [φ_L]; omega) fun ρ hρ => ?_
        obtain ⟨_, hm_eq⟩ := Finset.mem_filter.mp hρ
        have hm_lt : (ρ : ℂ).im - T / 2 < (m : ℝ) + 1 := by
          rw [← hm_eq]; exact Nat.lt_floor_add_one _
        have hcast : (φ_L m : ℝ) = (N_γ : ℝ) - 1 - (m : ℝ) := by
          dsimp [φ_L]
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
        rw [abs_sub_comm]
        exact (by rw [hcast]; linarith : (φ_L m : ℝ) ≤ γ - (ρ : ℂ).im).trans (le_abs_self _)
      calc ∑ m ∈ R_left, fibSum m
          ≤ ∑ m ∈ R_left, C₁ ^ 2 * K₂ * B * (1 / (φ_L m : ℝ) ^ 2) := Finset.sum_le_sum hterm_L
        _ = C₁ ^ 2 * K₂ * B * ∑ k ∈ R_left.image φ_L, 1 / (k : ℝ) ^ 2 := by
            rw [Finset.sum_image hinj_L, ← Finset.mul_sum]
        _ ≤ C₁ ^ 2 * K₂ * B * S_zeta2 :=
            mul_le_mul_of_nonneg_left
              (hinv_sq_sum.sum_le_tsum _ fun _ _ => by positivity) (by positivity)
    -- Right tail `R_right`: map `m ↦ m - (N_γ + 1) ≥ 1` injectively into `ℕ`
    have hright_le : ∑ m ∈ R_right, fibSum m ≤ C₁ ^ 2 * K₂ * B * S_zeta2 := by
      let φ_R : ℕ → ℕ := fun m => m - (N_γ + 1)
      have hinj_R : Set.InjOn φ_R (R_right : Set ℕ) := by
        intro a ha b hb hab
        have ha' : ¬ a ≤ N_γ + 1 := (Finset.mem_filter.mp ha).2.2
        have hb' : ¬ b ≤ N_γ + 1 := (Finset.mem_filter.mp hb).2.2
        dsimp [φ_R] at hab; omega
      have hterm_R : ∀ m ∈ R_right, fibSum m ≤ C₁ ^ 2 * K₂ * B * (1 / (φ_R m : ℝ) ^ 2) := by
        intro m hm
        have hm' : ¬ m ≤ N_γ + 1 := (Finset.mem_filter.mp hm).2.2
        refine hfib_sep m (φ_R m) (by dsimp [φ_R]; omega) fun ρ hρ => ?_
        obtain ⟨hρ_hi, hm_eq⟩ := Finset.mem_filter.mp hρ
        have him_ge : T / 2 ≤ (ρ : ℂ).im := not_lt.mp (Finset.mem_filter.mp hρ_hi).2
        have hm_le : (m : ℝ) ≤ (ρ : ℂ).im - T / 2 := by
          rw [← hm_eq]; exact Nat.floor_le (by linarith)
        have hcast : (φ_R m : ℝ) = (m : ℝ) - ((N_γ : ℝ) + 1) := by
          dsimp [φ_R]
          rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        exact (by rw [hcast]; linarith : (φ_R m : ℝ) ≤ (ρ : ℂ).im - γ).trans (le_abs_self _)
      calc ∑ m ∈ R_right, fibSum m
          ≤ ∑ m ∈ R_right, C₁ ^ 2 * K₂ * B * (1 / (φ_R m : ℝ) ^ 2) := Finset.sum_le_sum hterm_R
        _ = C₁ ^ 2 * K₂ * B * ∑ k ∈ R_right.image φ_R, 1 / (k : ℝ) ^ 2 := by
            rw [Finset.sum_image hinj_R, ← Finset.mul_sum]
        _ ≤ C₁ ^ 2 * K₂ * B * S_zeta2 :=
            mul_le_mul_of_nonneg_left
              (hinv_sq_sum.sum_le_tsum _ fun _ _ => by positivity) (by positivity)
    dsimp [B_high]
    linarith
  exact add_le_add hlow_le hhigh_le

/-- **Theorem 3b (`heckeDefect_log_unitWindow_tfae` — 5-Way Equivalence Collapsing `Π_{F_{c log T}}`).**
For EVERY `c > 0` and EVERY `α ≥ 0`, the following five conditions are equivalent (`TFAE`):
1. Uniform modulus prime-polynomial bound `E_γ(c log T) ≤ α ‖Π_{F_{c log T}}‖ + C` on `[T, T + 1)`;
2. Uniform signed prime-polynomial bound `E_γ(c log T) ≤ -α Re Π_{F_{c log T}} + C` on `[T, T + 1)`;
3. Uniform pure-constant bound `E_γ(c log T) ≤ B` on `[T, T + 1)` (`Π_{F_{c log T}}` absorbed);
4. Unit-window `L¹` bound `∫_{T}^{T+1} E_γ(c log T) dγ ≤ B`;
5. Unit-window depth-charge bound `unitWindowDepthCharge T (c log T) ≤ B`. -/
theorem heckeDefect_log_unitWindow_tfae {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α) :
    [(∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
          α * ‖primePolynomial (heckeAvgBump (c * Real.log T))
            ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C),
     (∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
          -α * (primePolynomial (heckeAvgBump (c * Real.log T))
            ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re + C),
     (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ B),
     (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        (∫ γ in Icc T (T + 1), heckeDefect (baseTwistTest γ) (c * Real.log T)) ≤ B),
     (∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        unitWindowDepthCharge T (c * Real.log T) ≤ B)].TFAE := by
  tfae_have 2 → 1 := by
    rintro ⟨C, hev⟩
    refine ⟨C, hev.mono fun T hT γ hγ => (hT γ hγ).trans ?_⟩
    set z := primePolynomial (heckeAvgBump (c * Real.log T))
      ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))
    have hle : -z.re ≤ ‖z‖ := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
    have := mul_le_mul_of_nonneg_left hle hα
    linarith
  tfae_have 1 → 4 := by
    rintro ⟨C, hev⟩
    obtain ⟨C₁, hC₁, hev_sa⟩ := exists_unitWindow_integral_norm_primePolynomial_le hc
    set C₂ : ℝ := 8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 + 1
    have hC₂_pos : 0 < C₂ := by
      have := cos_three_quarters_sq_pos
      dsimp [C₂]; positivity
    have hlog_ev : ∀ᶠ T : ℝ in atTop, 2 * α * C₂ ≤ c * Real.log T :=
      (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop (2 * α * C₂)
    have hlog1 : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
      (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
    refine ⟨2 * (α * C₁ + |C|), by positivity, ?_⟩
    filter_upwards [hev, hev_sa, hlog_ev, hlog1, eventually_ge_atTop (2 : ℝ)]
      with T hT hsa hsmall hL1 hT2
    set L : ℝ := c * Real.log T
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hint_E := integrableOn_heckeDefect_Icc T (T + 1) L
    have hcont_pp := continuous_norm_primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
    have hint_pp : IntegrableOn
        (fun γ : ℝ => ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
          (-γ / (2 * Real.pi))‖) (Icc T (T + 1)) volume :=
      hcont_pp.continuousOn.integrableOn_compact isCompact_Icc
    have hint_C : IntegrableOn (fun _ : ℝ => |C|) (Icc T (T + 1)) volume :=
      integrableOn_const (by simp)
    have hint_rhs : IntegrableOn
        (fun γ : ℝ => α * ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
          (-γ / (2 * Real.pi))‖ + |C|) (Icc T (T + 1)) volume :=
      (hint_pp.const_mul α).add hint_C
    have hmono := setIntegral_mono_on hint_E hint_rhs measurableSet_Icc
      (fun γ hγ => (hT γ hγ).trans (add_le_add le_rfl (le_abs_self C)))
    have hvol : volume.real (Icc T (T + 1)) = 1 := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    rw [integral_add (hint_pp.const_mul α) hint_C,
      integral_const_mul, setIntegral_const, hvol, one_smul] at hmono
    set I_E := ∫ γ in Icc T (T + 1), heckeDefect (baseTwistTest γ) L
    have hIE_nn : 0 ≤ I_E :=
      setIntegral_nonneg measurableSet_Icc fun _ _ => heckeDefect_nonneg _ _
    have hα_sa : α * (∫ γ in Icc T (T + 1),
        ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖) ≤
        α * C₁ + (α * (C₂ / L)) * I_E := by
      have := mul_le_mul_of_nonneg_left hsa hα
      dsimp [C₂, L, I_E] at this ⊢
      linarith
    have hcoeff : α * (C₂ / L) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hLpos zero_lt_two]
      dsimp [L]; linarith
    have hhalf : (α * (C₂ / L)) * I_E ≤ (1 / 2) * I_E :=
      mul_le_mul_of_nonneg_right hcoeff hIE_nn
    linarith
  tfae_have 4 → 5 := by
    rintro ⟨B, hB, hev⟩
    have hcos_pos := cos_quarter_sq_pos
    refine ⟨B / Real.cos (1 / 4 : ℝ) ^ 2, by positivity, ?_⟩
    filter_upwards [hev] with T hTB
    set L : ℝ := c * Real.log T
    have hint_E := integrableOn_heckeDefect_Icc T (T + 1) L
    have hint_dc : IntegrableOn
        (fun _ : ℝ => Real.cos (1 / 4 : ℝ) ^ 2 *
          ∑ ρ ∈ xiUnitWindowZeros T, ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2))
        (Icc T (T + 1)) volume :=
      integrableOn_const (by simp)
    have hmono := setIntegral_mono_on hint_dc hint_E measurableSet_Icc
      (fun γ hγ => unitWindow_depthCharge_le_heckeDefect T L hγ.1 hγ.2)
    have hvol : volume.real (Icc T (T + 1)) = 1 := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    rw [setIntegral_const, hvol, one_smul] at hmono
    exact (le_div_iff₀' hcos_pos).mpr (hmono.trans hTB)
  tfae_have 5 → 3 := fun ⟨B, hB, hev⟩ =>
    eventually_heckeDefect_le_of_unitWindowDepthCharge_le hc hB hev
  tfae_have 3 → 2 := by
    rintro ⟨B, hB, hev⟩
    obtain ⟨C_neg, hCneg, hneg⟩ := neg_re_primePolynomial_ge_of_heckeDefect_le hc hB
    have hlog1 : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
      (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
    refine ⟨B + α * C_neg, ?_⟩
    filter_upwards [hev, hlog1, eventually_ge_atTop (2 : ℝ)] with T hTB hL1 hT2 γ hγ
    have hEB := hTB γ hγ
    have hn := hneg T γ hT2 hL1 hγ.1 hγ.2 hEB
    have hαn := mul_le_mul_of_nonneg_left hn hα
    linarith
  tfae_finish

/-- **Theorem 3c (`eventually_heckeDefect_le_pos_re_primePolynomial_iff` — Exact Positive-Sign
Separation).**
For `c > 0` and `α > 0`, the opposite-sign bound
`E_γ(c log T) ≤ +α * (primePolynomial F_{c log T} N*(c log T) (-γ / 2π)).re + C`
holds uniformly on `[T, T + 1)` eventually in `T` IF AND ONLY IF both `E_γ(c log T)` AND
`collidedForm zetaZeroConfig (twist γ F_{c log T})` are bounded `O(1)` uniformly on `[T, T + 1)`
(which in particular forces bounded horizontal fibre multiplicity `H(γ) = O(1)`). -/
theorem eventually_heckeDefect_le_pos_re_primePolynomial_iff {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    (∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
        α * (primePolynomial (heckeAvgBump (c * Real.log T))
          ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re + C) ↔
    ((∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤ B) ∧
     (∃ B_c : ℝ, 0 ≤ B_c ∧ ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        collidedForm zetaZeroConfig (twist γ (heckeAvgBump (c * Real.log T))) ≤ B_c)) := by
  obtain ⟨C_arch, hCarch, harch_bd⟩ := exists_abs_re_archPart_heckeAvgBump_log_le hc
  have hlog1 : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
  constructor
  · rintro ⟨C, hev_pos⟩
    -- First deduce `(1)` (`E_γ ≤ α ‖Π‖ + C`), hence `(3)` (`E_γ ≤ B`) via `heckeDefect_log_unitWindow_tfae`
    have hev_mod : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
          α * ‖primePolynomial (heckeAvgBump (c * Real.log T))
            ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C := by
      refine ⟨C, hev_pos.mono fun T hT γ hγ => (hT γ hγ).trans ?_⟩
      set z := primePolynomial (heckeAvgBump (c * Real.log T))
        ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))
      have hle : z.re ≤ ‖z‖ := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
      linarith [mul_le_mul_of_nonneg_left hle hα.le]
    obtain ⟨B, hB, hev_B⟩ :=
      ((heckeDefect_log_unitWindow_tfae hc hα.le).out 0 2).mp hev_mod
    refine ⟨⟨B, hB, hev_B⟩, ?_⟩
    have hsinc_pos := sincLorentzConst_pos
    set B_off : ℝ := 4 * B + sincLorentzConst * (1 + 4 / c)
    refine ⟨C_arch + B_off + |C| / α, by positivity, ?_⟩
    filter_upwards [hev_pos, hev_B, hlog1, eventually_ge_atTop (2 : ℝ)] with T hpos hTB hL1 hT2 γ hγ
    set L : ℝ := c * Real.log T
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    set ξ : ℝ := -γ / (2 * Real.pi)
    have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
      (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hLpos) ξ
    have htw : twist γ (heckeAvgBump L) = heightShift ξ (heckeAvgBump L) := twist_eq_heightShift γ _
    have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
      (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
    have hcap := re_W_eq_collided_sub_defect (Z := zetaZeroConfig) hs
    rw [htw] at hcap
    have harch := (abs_le.mp (harch_bd T γ hT2 hL1 hγ.1 hγ.2)).2
    have hdef := offLineDefect_heckeAvg_le_heckeDefect_add_lorentz hLpos γ
    -- Bound `offLineDefect ≤ B_off`
    have hT0 : 0 ≤ T := by linarith
    have habsγ : |γ| = γ := abs_of_pos (by linarith [hγ.1])
    have hγ4 : γ + 4 ≤ T ^ 4 := by
      have : 0 ≤ (T - 2) * (T ^ 3 + 2 * T ^ 2 + 4 * T + 7) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hγ.2]
    have hlog4 : Real.log (|γ| + 4) ≤ 4 * Real.log T := by
      rw [habsγ]
      calc Real.log (γ + 4) ≤ Real.log (T ^ 4) := Real.log_le_log (by linarith [hγ.1]) hγ4
        _ = 4 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have hlogT_ne : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
    have htail : sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 ≤
        sincLorentzConst * (1 + 4 / c) := by
      calc sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2
          ≤ sincLorentzConst * (1 + 4 * Real.log T) / L ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hsinc_pos.le)
              (sq_nonneg _)
        _ ≤ sincLorentzConst * (1 + 4 * Real.log T) / L :=
            div_le_div_of_nonneg_left
              (mul_nonneg hsinc_pos.le (by linarith [Real.log_nonneg (by linarith : 1 ≤ T)]))
              hLpos hLsq
        _ = sincLorentzConst / L + sincLorentzConst * ((4 * Real.log T) / (c * Real.log T)) := by
            dsimp [L]; ring
        _ ≤ sincLorentzConst + sincLorentzConst * (4 / c) := by
            have hd1 : sincLorentzConst / L ≤ sincLorentzConst := div_le_self hsinc_pos.le hL1
            have hd2 : (4 * Real.log T) / (c * Real.log T) = 4 / c := by field_simp
            rw [hd2]; linarith
        _ = sincLorentzConst * (1 + 4 / c) := by ring
    have hoff_le : offLineDefect zetaZeroConfig (twist γ (heckeAvgBump L)) ≤ B_off := by
      have hEB := hTB γ hγ
      dsimp [B_off]; linarith
    -- From `0 ≤ E_γ ≤ α * Re Π + C` and `Re Π + collidedForm = Re A + offLineDefect`:
    rw [← htw] at hEF hcap
    have hre_le : (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ ξ).re ≤
        C_arch + B_off - collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)) := by
      linarith
    have h0_le_pos : 0 ≤ α * (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ ξ).re + |C| :=
      (heckeDefect_nonneg _ _).trans ((hpos γ hγ).trans (add_le_add le_rfl (le_abs_self C)))
    have hmul_le := mul_le_mul_of_nonneg_left hre_le hα.le
    have hα_coll : α * collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)) ≤
        α * (C_arch + B_off) + |C| := by linarith
    rw [show C_arch + B_off + |C| / α = (α * (C_arch + B_off) + |C|) / α by field_simp]
    exact (le_div_iff₀' hα).mpr hα_coll
  · rintro ⟨⟨B, _, hev_B⟩, ⟨B_c, _, hev_c⟩⟩
    refine ⟨B + α * (C_arch + B_c), ?_⟩
    filter_upwards [hev_B, hev_c, hlog1, eventually_ge_atTop (2 : ℝ)] with T hTB hTc hL1 hT2 γ hγ
    set L : ℝ := c * Real.log T
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    set ξ : ℝ := -γ / (2 * Real.pi)
    have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
      (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hLpos) ξ
    have htw : twist γ (heckeAvgBump L) = heightShift ξ (heckeAvgBump L) := twist_eq_heightShift γ _
    have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
      (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
    have hcap := re_W_eq_collided_sub_defect (Z := zetaZeroConfig) hs
    rw [← htw] at hEF
    have hdef_nn : 0 ≤ offLineDefect zetaZeroConfig (twist γ (heckeAvgBump L)) :=
      tsum_nonneg fun _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _)
    have harch_lo : -C_arch ≤ (archPart (heckeAvgBump L) ξ).re :=
      (abs_le.mp (harch_bd T γ hT2 hL1 hγ.1 hγ.2)).1
    have hcoll_hi := hTc γ hγ
    have hre_ge : -(C_arch + B_c) ≤
        (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ ξ).re := by
      linarith
    have hα_ge := mul_le_mul_of_nonneg_left hre_ge hα.le
    have hEB := hTB γ hγ
    linarith

/-! ## §4. Logarithmic zero-free corridor, `ZerosApproachLine`, and `LindelofCriticalLine` -/

/-- **Theorem 3d (`exists_log_zeroFree_corridor_of_heckeDefect_bound` — Classical Logarithmic
Zero-Free Corridor).**
If `unitWindowDepthCharge T (c * log T) ≤ B` eventually in `T` (equivalently, any of the 5 TFAE
conditions of `heckeDefect_log_unitWindow_tfae`), then there exist `T₁ ≥ 2` and `A > 0` such that
every zero `ρ ∈ zetaZeroConfig.carrier` with `|ρ.im| ≥ T₁` satisfies
`|ρ.re - 1/2| ≤ A / Real.log |ρ.im|`. -/
theorem exists_log_zeroFree_corridor_of_heckeDefect_bound {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hev : ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (c * Real.log T) ≤ B) :
    ∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, T₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im| := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (4 : ℝ)))
  set A : ℝ := (Real.sqrt B + 1) / c
  have hA_pos : 0 < A := by dsimp [A]; positivity
  refine ⟨T₀ + 2, A, by linarith [(hT₀ T₀ le_rfl).2], hA_pos, ?_⟩
  -- First prove for positive ordinates `ρ.im ≥ T₀ + 2`, then extend by conjugation symmetry
  have hpos_im : ∀ ρ ∈ zetaZeroConfig.carrier, T₀ + 2 ≤ ρ.im →
      |ρ.re - 1 / 2| ≤ A / Real.log ρ.im := by
    intro ρ hρ him
    have him_ge4 : 4 ≤ ρ.im := by linarith [(hT₀ T₀ le_rfl).2]
    set U : ℝ := ρ.im - 1 / 2
    have hU_ge_T₀ : T₀ ≤ U := by dsimp [U]; linarith
    obtain ⟨hxi, h0, h1⟩ :=
      CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ
    have hmem_W : ρ ∈ xiUnitWindowZeros U := by
      rw [mem_xiUnitWindowZeros]
      exact ⟨(Set.Finite.mem_toFinset _).mpr ⟨⟨h0, h1, by linarith, by dsimp [U]; linarith⟩, hxi⟩,
        by dsimp [U]; linarith⟩
    have hdk_le : depthKernel (c * Real.log U) (ρ.re - 1 / 2) ≤ B :=
      (depthKernel_le_unitWindowDepthCharge hmem_W).trans (hT₀ U hU_ge_T₀).1
    have hquad := (quadratic_le_depthKernel (c * Real.log U) (ρ.re - 1 / 2)).trans hdk_le
    have hsq_le : (2 * (c * Real.log U) * |ρ.re - 1 / 2|) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      rw [Real.sq_sqrt hB]
      calc (2 * (c * Real.log U) * |ρ.re - 1 / 2|) ^ 2
          = 4 * (c * Real.log U) ^ 2 * |ρ.re - 1 / 2| ^ 2 := by ring
        _ = 4 * (c * Real.log U) ^ 2 * (ρ.re - 1 / 2) ^ 2 := by rw [sq_abs]
        _ ≤ B := hquad
    have hprod_le : 2 * (c * Real.log U) * |ρ.re - 1 / 2| ≤ Real.sqrt B := by
      by_contra hlt
      have hgt := pow_lt_pow_left₀ (not_le.mp hlt) (Real.sqrt_nonneg B) (by norm_num : 2 ≠ 0)
      linarith
    -- Since `ρ.im ≥ 4`, `ρ.im ≤ U ^ 2`, so `Real.log ρ.im ≤ 2 * Real.log U`
    have him_le_sq : ρ.im ≤ U ^ 2 := by dsimp [U]; nlinarith
    have hlog_im_le : Real.log ρ.im ≤ 2 * Real.log U := by
      calc Real.log ρ.im ≤ Real.log (U ^ 2) := Real.log_le_log (by linarith) him_le_sq
        _ = 2 * Real.log U := by rw [Real.log_pow]; push_cast; rfl
    have hlog_im_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlog_im_pos]
    have h1 : c * Real.log ρ.im * |ρ.re - 1 / 2| ≤ 2 * (c * Real.log U) * |ρ.re - 1 / 2| := by
      have : c * Real.log ρ.im ≤ 2 * (c * Real.log U) := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h2 : c * (|ρ.re - 1 / 2| * Real.log ρ.im) ≤ Real.sqrt B + 1 := by linarith
    have hc_ne : c ≠ 0 := hc.ne'
    have hA_eq : c * A = Real.sqrt B + 1 := by dsimp [A]; field_simp
    nlinarith
  intro ρ hρ habs
  rcases le_or_gt 0 ρ.im with him0 | him_neg
  · rw [abs_of_nonneg him0] at habs ⊢
    exact hpos_im ρ hρ habs
  · have hc_mem : conj ρ ∈ zetaZeroConfig.carrier := conj_mem_zetaZeroConfig hρ
    have hconj_im : (conj ρ).im = -ρ.im := Complex.conj_im ρ
    have habs_eq : |ρ.im| = -ρ.im := abs_of_neg him_neg
    rw [habs_eq] at habs ⊢
    have hres := hpos_im (conj ρ) hc_mem (by rw [hconj_im]; exact habs)
    rwa [Complex.conj_re, hconj_im] at hres

/-- **Theorem 3e (`zerosApproachLine_and_lindelof_of_heckeDefect_log_bound`).**
Any uniform prime-polynomial or `O(1)` bound on `heckeDefect (baseTwistTest γ) (c * log T)` across
`[T, T + 1)` (`c > 0`, `α ≥ 0`) forces `ZerosApproachLine`, `OffLineSparse`, `LindelofCriticalLine`,
and a strict zero-free half-plane `∃ β < 1/2, XiZeroHalfPlaneBound β`. -/
theorem zerosApproachLine_and_lindelof_of_heckeDefect_log_bound {c α : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α)
    (hhyp : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
        α * ‖primePolynomial (heckeAvgBump (c * Real.log T))
          ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C) :
    ZerosApproachLine ∧ OffLineSparse ∧ LindelofCriticalLine ∧
      (∃ β : ℝ, β < 1 / 2 ∧ XiZeroHalfPlaneBound β) := by
  obtain ⟨B, hB, hev_w⟩ := ((heckeDefect_log_unitWindow_tfae hc hα).out 0 4).mp hhyp
  obtain ⟨T₁, A, hT₁2, hA, hcorr⟩ := exists_log_zeroFree_corridor_of_heckeDefect_bound hc hB hev_w
  have hZ : ZerosApproachLine := by
    intro h hh
    set M_h : ℝ := max T₁ (Real.exp (A / h) + 1)
    refine (xiZeroBall (⌈M_h + 2⌉₊)).finite_toSet.subset fun q hq => ?_
    have hq_im : h < (xiSpectralPoint q).im := hq
    simp only [Finset.mem_coe, mem_xiZeroBall]
    have hmem_z : (q.1 : ℂ) ∈ zetaZeroConfig.carrier :=
      CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
        ⟨xi_xiZeroCopy_eq_zero q, xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩
    have hsp_im : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint]
    have hdepth_gt : h < |(q.1 : ℂ).re - 1 / 2| := by
      rw [abs_sub_comm]
      exact lt_of_lt_of_le (by linarith : h < 1 / 2 - (q.1 : ℂ).re) (le_abs_self _)
    -- Therefore `|(q.1 : ℂ).im| < M_h`, otherwise the corridor gives `|(q.1).re - 1/2| ≤ h`
    have him_lt : |(q.1 : ℂ).im| < M_h := by
      by_contra hge
      have hge' : M_h ≤ |(q.1 : ℂ).im| := not_lt.mp hge
      have hge_T₁ : T₁ ≤ |(q.1 : ℂ).im| := (le_max_left _ _).trans hge'
      have hge_exp : Real.exp (A / h) < |(q.1 : ℂ).im| :=
        lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hge')
      have hlog_gt : A / h < Real.log |(q.1 : ℂ).im| := by
        rw [← Real.log_exp (A / h)]
        exact Real.log_lt_log (Real.exp_pos _) hge_exp
      have hlog_pos : 0 < Real.log |(q.1 : ℂ).im| :=
        lt_trans (div_pos hA hh) hlog_gt
      have hcorr_q := hcorr (q.1 : ℂ) hmem_z hge_T₁
      have hdiv_lt : A / Real.log |(q.1 : ℂ).im| < h := by
        rw [div_lt_iff₀ hlog_pos]
        have := (div_lt_iff₀ hh).mp hlog_gt
        linarith
      linarith
    rw [norm_xiSpectralPoint]
    have hnorm : ‖(q.1 : ℂ) - 1 / 2‖ ≤ |(q.1 : ℂ).re - 1 / 2| + |(q.1 : ℂ).im| := by
      have := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
      simpa using this
    have hre_le : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have hceil : M_h + 2 ≤ (⌈M_h + 2⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  exact ⟨hZ, offLineSparse_of_zerosApproachLine hZ,
    lindelofCriticalLine_of_zerosApproachLine hZ, quasiRH_of_zerosApproachLine hZ⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_div_pow_of_finiteOffLine
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_primePolynomial_any_cutoff_of_finiteOffLine
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_heckeDefect_log_le_neg_re_primePolynomial_of_finiteOffLine
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindowDepthCharge_log_iff_of_pos
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.heckeDefect_log_unitWindow_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.eventually_heckeDefect_le_pos_re_primePolynomial_iff
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_log_zeroFree_corridor_of_heckeDefect_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.zerosApproachLine_and_lindelof_of_heckeDefect_log_bound
