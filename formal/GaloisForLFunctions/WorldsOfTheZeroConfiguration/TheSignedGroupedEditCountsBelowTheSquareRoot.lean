import GaloisForLFunctions.WorldsOfTheZeroConfiguration.FakeEditsWithSubpolynomialDefectEnergy
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheNormCountOfAnEditIsAConvolution
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ACountBelowTheDeletionExponentIsARealZero
import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift
import GaloisForLFunctions.BezoutValuationIncidence.HyperbolaCancellationWithDivisorBoundedCoefficients

/-!
# The signed grouped edit counts below the square root

The system of an edit is `ζ_B = ζ · M_B`, and its norm count is `1 * u` with the twin coefficients
`u = μ_S * 1_{T-numbers}` (`S` the deleted, `T` the doubled primes).  Since `S ∩ T = ∅`, an integer
has at most one factorization into an `S`-number and a `T`-number, so `|u| ≤ 1`
(`abs_twinCoeff_le_one`), and `L(u, s) = M_B(s)` (`LSeries_twin_eq`).

* **The hyperbola count** (`exists_abs_sum_mul_zeta_sub_le`).  If `|Σ_{j ≤ n} u(j)| ≤ C n^θ`,
  `θ < 1`, and `Σ_{j ≤ n} |u(j)| ≤ Z n^a`, `θ ≤ a`, then
  `Σ_{n ≤ N} (u * 1)(n) = A N + O(N^{a/(1+a−θ)})`.  Split `Σ_m u(m) ⌊N/m⌋` at `D = N^{1/(1+a−θ)}`:
  below `D` write `⌊N/m⌋ = N/m − {N/m}`; the main term is `N Σ_{m ≤ D} u(m)/m = A N + O(N D^{θ−1})`
  by summation by parts, the fractional parts cost `Z D^a`; above `D` swap the sums, each block is
  a difference of partial sums and the blocks cost `O(N D^{θ−1})`.
* **The cofactor left of the line** (`exists_norm_editCofactor_le_of_re`).  `M_B` is
  subpolynomial on `σ₀ ≤ Re s ≤ 2` for every `σ₀ > max(α/2, β − ½, Θ + β − 1)`.
* **Partial sums of the twin coefficients** (`exists_abs_sum_twin_le`).  The smoothed Perron
  shift of `L(u, s) = M_B(s)` to `Re s = σ₀` gives `Σ_{j ≤ n} u(j) ≪ n^{(ε+σ₀)/(1+ε)+κ}`.
* **The theorem** (`exists_isIntegerNormFakeAt_sEdit_lt_half`).  With `Θ = zetaZeroAbscissa`, for
  every `½ < β < 2/3` with `Θ + 2β < 2` and `ζ(β + iγ) ≠ 0` the signed grouped edit with zero pair
  `β ± iγ` is an integer-norm fake at a count exponent `c < ½`; its continuation `(s − 1)ζ_B` has
  exactly the zeros of `(s − 1)ζ(s)` and `β ± iγ` right of an abscissa `σ₁ < ½`.

The Rankin mass of `u` gives `a` just above `β`, the Perron shift gives `θ` just above
`σ₀ ≈ max(β/2, Θ + β − 1)`, and `a + θ < 1` is `Θ + 2β < 2`.
-/

open Complex Finset Filter Topology
open RHTower RHTower.Sieve RHTower.BeurlingDeletion
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.NormCount
open GaloisForLFunctions.ArithmeticPositiveDuality GaloisForLFunctions.EulerFETransportTheory
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.RigidArithmeticOfCuts

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-! ## The hyperbola count -/

/-- `x/2 ≤ ⌊x⌋` for `x ≥ 1`. -/
theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx)
  have h2 := Nat.lt_floor_add_one x
  linarith

/-- **Summation by parts against `1/m`.**  With `U(n) = Σ_{0<j≤n} f(j)`,
`Σ_{D<m≤M} f(m)/m = U(M)/(M+1) − U(D)/(D+1) + Σ_{D<m≤M} U(m)(1/m − 1/(m+1))`. -/
theorem sum_Ioc_div_eq (f : ℕ → ℝ) {D M : ℕ} (hDM : D ≤ M) :
    ∑ m ∈ Ioc D M, f m / m =
      (∑ j ∈ Ioc 0 M, f j) / (M + 1) - (∑ j ∈ Ioc 0 D, f j) / (D + 1) +
        ∑ m ∈ Ioc D M, (∑ j ∈ Ioc 0 m, f j) * (1 / m - 1 / (m + 1)) := by
  induction M, hDM using Nat.le_induction with
  | base => simp
  | succ M hDM ih =>
    rw [Finset.sum_Ioc_succ_top hDM, Finset.sum_Ioc_succ_top hDM, ih,
      Finset.sum_Ioc_succ_top (Nat.zero_le M)]
    push_cast
    ring

/-- **The tail of `Σ f(m)/m` from power partial sums.**  If `|U(n)| ≤ C n^θ`, `θ < 1`, then
`|Σ_{D<m≤M} f(m)/m| ≤ C (2 + 1/(1−θ)) D^{θ−1}`. -/
theorem abs_sum_Ioc_div_le {f : ℕ → ℝ} {C θ : ℝ} (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hU : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Ioc 0 n, f j| ≤ C * (n : ℝ) ^ θ) {D M : ℕ} (hD : 1 ≤ D)
    (hDM : D ≤ M) :
    |∑ m ∈ Ioc D M, f m / m| ≤ C * (2 + 1 / (1 - θ)) * (D : ℝ) ^ (θ - 1) := by
  rw [sum_Ioc_div_eq f hDM]
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hM : 1 ≤ M := le_trans hD hDM
  have hpow : ∀ n : ℕ, 1 ≤ n → C * (n : ℝ) ^ θ / (n + 1) ≤ C * (n : ℝ) ^ (θ - 1) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_sub_one hn0.ne', div_le_iff₀ (by positivity)]
    have e : C * ((n : ℝ) ^ θ / n) * (n + 1) = C * (n : ℝ) ^ θ + C * (n : ℝ) ^ θ / n := by
      field_simp
    have : 0 ≤ C * (n : ℝ) ^ θ / n := div_nonneg (mul_nonneg hC (Real.rpow_nonneg hn0.le _)) hn0.le
    linarith
  have hmono : ∀ n : ℕ, D ≤ n → (n : ℝ) ^ (θ - 1) ≤ (D : ℝ) ^ (θ - 1) := fun n hn =>
    Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast hn) (by linarith)
  have hend : ∀ n : ℕ, D ≤ n → |(∑ j ∈ Ioc 0 n, f j) / (n + 1)| ≤ C * (D : ℝ) ^ (θ - 1) := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hD hn
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    calc |∑ j ∈ Ioc 0 n, f j| / (n + 1) ≤ C * (n : ℝ) ^ θ / (n + 1) := by
          gcongr; exact hU n hn1
      _ ≤ C * (n : ℝ) ^ (θ - 1) := hpow n hn1
      _ ≤ C * (D : ℝ) ^ (θ - 1) := mul_le_mul_of_nonneg_left (hmono n hn) hC
  have h1 := hend M hDM
  have h2 := hend D le_rfl
  have h3 : |∑ m ∈ Ioc D M, (∑ j ∈ Ioc 0 m, f j) * (1 / m - 1 / (m + 1))| ≤
      C / (1 - θ) * (D : ℝ) ^ (θ - 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ Ioc D M, |(∑ j ∈ Ioc 0 m, f j) * (1 / m - 1 / (m + 1))| ≤
        C * (m : ℝ) ^ (-(1 + (1 - θ))) := by
      intro m hm
      have hm1 : 1 ≤ m := le_trans hD (Finset.mem_Ioc.mp hm).1.le
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hdiff : 1 / (m : ℝ) - 1 / (m + 1) = 1 / (m * (m + 1)) := by field_simp; ring
      have hle : 1 / ((m : ℝ) * (m + 1)) ≤ 1 / (m * m) :=
        one_div_le_one_div_of_le (mul_pos hm0 hm0) (by nlinarith)
      rw [abs_mul, hdiff, abs_of_pos (div_pos one_pos (mul_pos hm0 (by linarith)))]
      calc |∑ j ∈ Ioc 0 m, f j| * (1 / (m * (m + 1))) ≤ C * (m : ℝ) ^ θ * (1 / (m * m)) :=
            mul_le_mul (hU m hm1) hle (by positivity) (mul_nonneg hC (Real.rpow_nonneg hm0.le _))
        _ = C * (m : ℝ) ^ (-(1 + (1 - θ))) := by
            rw [show -(1 + (1 - θ)) = θ - 2 by ring, Real.rpow_sub hm0, Real.rpow_two]
            ring
    calc ∑ m ∈ Ioc D M, |(∑ j ∈ Ioc 0 m, f j) * (1 / m - 1 / (m + 1))|
        ≤ ∑ m ∈ Ioc D M, C * (m : ℝ) ^ (-(1 + (1 - θ))) := Finset.sum_le_sum hterm
      _ = C * ∑ m ∈ Ioc D M, (m : ℝ) ^ (-(1 + (1 - θ))) := by rw [Finset.mul_sum]
      _ ≤ C * ((D : ℝ) ^ (-(1 - θ)) / (1 - θ)) :=
          mul_le_mul_of_nonneg_left
            (BezoutValuationIncidence.sum_Ioc_rpow_neg_one_sub_le (by linarith) hD) hC
      _ = C / (1 - θ) * (D : ℝ) ^ (θ - 1) := by
          rw [show -(1 - θ) = θ - 1 by ring]; ring
  have htri := (abs_add_le (((∑ j ∈ Ioc 0 M, f j) / (M + 1)) - (∑ j ∈ Ioc 0 D, f j) / (D + 1))
    (∑ m ∈ Ioc D M, (∑ j ∈ Ioc 0 m, f j) * (1 / m - 1 / (m + 1)))).trans
    (add_le_add (abs_sub _ _) le_rfl)
  have e : C * (2 + 1 / (1 - θ)) * (D : ℝ) ^ (θ - 1) =
      C * (D : ℝ) ^ (θ - 1) + C * (D : ℝ) ^ (θ - 1) + C / (1 - θ) * (D : ℝ) ^ (θ - 1) := by ring
  linarith

/-- **The hyperbola count.**  Let `f` have partial sums `|Σ_{0<j≤n} f(j)| ≤ C n^θ` (`θ < 1`) and
absolute mass `Σ_{0<j≤n} |f(j)| ≤ Z n^a` (`θ ≤ a`, `a > 0`).  Then
`Σ_{0<n≤N} (f * 1)(n) = A N + O(N^{a/(1+a−θ)})`. -/
theorem exists_abs_sum_mul_zeta_sub_le (f : ArithmeticFunction ℝ) {C Z θ a : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθa : θ ≤ a) (ha0 : 0 < a) (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hU : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Ioc 0 n, f j| ≤ C * (n : ℝ) ^ θ)
    (hR : ∀ n : ℕ, 1 ≤ n → ∑ j ∈ Ioc 0 n, |f j| ≤ Z * (n : ℝ) ^ a) :
    ∃ A K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Ioc 0 N, (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n - A * N| ≤
        K * (N : ℝ) ^ (a / (1 + a - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  set K₁ : ℝ := C * (2 + 1 / (1 - θ)) with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hC (by have := one_div_pos.mpr h1θ; linarith)
  set V : ℕ → ℝ := fun D => ∑ m ∈ Ioc 0 D, f m / m with hV
  have hVdiff : ∀ D M : ℕ, 1 ≤ D → D ≤ M → |V M - V D| ≤ K₁ * (D : ℝ) ^ (θ - 1) := by
    intro D M hD hDM
    have hsplit : V M - V D = ∑ m ∈ Ioc D M, f m / m := by
      simp only [hV]
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDM]
      ring
    rw [hsplit]
    exact abs_sum_Ioc_div_le hθ1 hC hU hD hDM
  -- `D^{θ−1} → 0`
  have htend : Tendsto (fun D : ℕ => K₁ * (D : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop h1θ).comp tendsto_natCast_atTop_atTop
    have h' := h.const_mul K₁
    rw [mul_zero] at h'
    refine h'.congr fun D => ?_
    simp only [Function.comp_apply]
    rw [show -(1 - θ) = θ - 1 by ring]
  -- `V` converges
  have hcauchy : CauchySeq V := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨D₀, hD₀⟩ := (eventually_atTop.mp
      ((htend.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)))
    refine ⟨D₀, fun M hM => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hVdiff D₀ M (hD₀ D₀ le_rfl).2 hM) (hD₀ D₀ le_rfl).1
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hVA : ∀ D : ℕ, 1 ≤ D → |V D - A| ≤ K₁ * (D : ℝ) ^ (θ - 1) := by
    intro D hD
    have hlim : Tendsto (fun M => |V M - V D|) atTop (𝓝 |A - V D|) :=
      (hA.sub_const (V D)).abs
    rw [abs_sub_comm]
    exact le_of_tendsto hlim (eventually_atTop.mpr ⟨D, fun M hM => hVdiff D M hD hM⟩)
  have hden : 0 < 1 + a - θ := by linarith
  have hden' : 1 + a - θ ≠ 0 := hden.ne'
  set lam : ℝ := 1 / (1 + a - θ) with hlam
  have hlam0 : 0 < lam := div_pos one_pos hden
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
  have hlamθ : 1 + lam * (θ - 1) = lam * a := by rw [hlam]; field_simp; ring
  refine ⟨A, (K₁ + 2 * C / (1 - θ)) * 2 ^ (1 - θ) + Z, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNl : 1 ≤ (N : ℝ) ^ lam := Real.one_le_rpow hN1 hlam0.le
  have hNlN : (N : ℝ) ^ lam ≤ N := by
    calc (N : ℝ) ^ lam ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hlam1
      _ = N := Real.rpow_one _
  set D : ℕ := ⌊(N : ℝ) ^ lam⌋₊ with hDdef
  have hD1 : 1 ≤ D := Nat.le_floor (by exact_mod_cast hNl)
  have hDN : D ≤ N := Nat.floor_le_of_le hNlN
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDle : (D : ℝ) ≤ (N : ℝ) ^ lam := Nat.floor_le (by positivity)
  have hDhalf : (N : ℝ) ^ lam / 2 ≤ D := half_le_floor hNl
  -- the floor sum, split at `D`
  rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f N,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDN]
  -- the head
  have hhead : ∑ d ∈ Ioc 0 D, f d * ((N / d : ℕ) : ℝ) =
      N * V D - ∑ d ∈ Ioc 0 D, f d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    simp only [hV]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hfrac : |∑ d ∈ Ioc 0 D, f d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| ≤ Z * (D : ℝ) ^ a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun d hd => ?_).trans
      (hR D hD1))
    have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hlo : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hhi : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
      have h := Nat.lt_div_mul_add (a := N) (b := d) hd1
      have h' : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
      rw [div_sub' hd0.ne', div_le_one hd0]
      linarith
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact mul_le_of_le_one_right (abs_nonneg _) hhi
  -- the tail: swap the sums
  have htail : |∑ d ∈ Ioc D N, f d * ((N / d : ℕ) : ℝ)| ≤
      2 * C / (1 - θ) * N * (D : ℝ) ^ (θ - 1) := by
    rw [BezoutValuationIncidence.sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc f D N]
    have hND : N / D ≤ N := Nat.div_le_self N D
    have hCN : 0 ≤ 2 * C * (N : ℝ) ^ θ :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hinner : ∀ k ∈ Icc 1 N, |∑ d ∈ Ioc D (N / k), f d| ≤
        if k ≤ N / D then 2 * C * (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) else 0 := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      split_ifs with hkD
      · by_cases hDk : D ≤ N / k
        · have hsplit : ∑ d ∈ Ioc D (N / k), f d =
              ∑ d ∈ Ioc 0 (N / k), f d - ∑ d ∈ Ioc 0 D, f d := by
            rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDk]; ring
          have hNk1 : 1 ≤ N / k := le_trans hD1 hDk
          have hcast : ((N / k : ℕ) : ℝ) ^ θ ≤ (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) := by
            calc ((N / k : ℕ) : ℝ) ^ θ ≤ ((N : ℝ) / k) ^ θ :=
                  Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hθ0
              _ = (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) := by
                  rw [Real.div_rpow hN0.le hk0.le, Real.rpow_neg hk0.le, div_eq_mul_inv]
          have hDθ : (D : ℝ) ^ θ ≤ ((N / k : ℕ) : ℝ) ^ θ :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hDk) hθ0
          rw [hsplit]
          calc |∑ d ∈ Ioc 0 (N / k), f d - ∑ d ∈ Ioc 0 D, f d|
              ≤ |∑ d ∈ Ioc 0 (N / k), f d| + |∑ d ∈ Ioc 0 D, f d| := abs_sub _ _
            _ ≤ C * ((N / k : ℕ) : ℝ) ^ θ + C * (D : ℝ) ^ θ :=
                add_le_add (hU _ hNk1) (hU D hD1)
            _ ≤ 2 * C * ((N / k : ℕ) : ℝ) ^ θ := by linarith [mul_le_mul_of_nonneg_left hDθ hC]
            _ ≤ 2 * C * ((N : ℝ) ^ θ * (k : ℝ) ^ (-θ)) :=
                mul_le_mul_of_nonneg_left hcast (by linarith)
            _ = 2 * C * (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) := by ring
        · rw [Finset.Ioc_eq_empty (by omega)]
          simp only [Finset.sum_empty, abs_zero]
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · have hlt : N < k * D := (Nat.div_lt_iff_lt_mul (by omega : 0 < D)).mp (by omega)
        have hle : N / k ≤ D := Nat.div_le_of_le_mul hlt.le
        rw [Finset.Ioc_eq_empty (by omega)]
        simp
    have hfilter : (Icc 1 N).filter (fun k => k ≤ N / D) = Icc 1 (N / D) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    calc |∑ k ∈ Icc 1 N, ∑ d ∈ Ioc D (N / k), f d|
        ≤ ∑ k ∈ Icc 1 N, |∑ d ∈ Ioc D (N / k), f d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 N, (if k ≤ N / D then 2 * C * (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) else 0) :=
          Finset.sum_le_sum hinner
      _ = ∑ k ∈ Icc 1 (N / D), 2 * C * (N : ℝ) ^ θ * (k : ℝ) ^ (-θ) := by
          rw [← Finset.sum_filter, hfilter]
      _ = 2 * C * (N : ℝ) ^ θ * ∑ k ∈ Icc 1 (N / D), (k : ℝ) ^ ((1 - θ) - 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show (1 - θ) - 1 = -θ by ring]
      _ ≤ 2 * C * (N : ℝ) ^ θ * (((N / D : ℕ) : ℝ) ^ (1 - θ) / (1 - θ)) :=
          mul_le_mul_of_nonneg_left (DeletionData.sum_rpow_le h1θ (by linarith) _) hCN
      _ ≤ 2 * C * (N : ℝ) ^ θ * (((N : ℝ) / D) ^ (1 - θ) / (1 - θ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le h1θ.le) h1θ.le) hCN
      _ = 2 * C / (1 - θ) * ((N : ℝ) ^ θ * (N : ℝ) ^ (1 - θ)) * ((D : ℝ) ^ (1 - θ))⁻¹ := by
          rw [Real.div_rpow hN0.le hD0.le]; ring
      _ = 2 * C / (1 - θ) * N * (D : ℝ) ^ (θ - 1) := by
          have hNN : (N : ℝ) ^ θ * (N : ℝ) ^ (1 - θ) = N := by
            rw [← Real.rpow_add hN0]; simp
          rw [hNN, show θ - 1 = -(1 - θ) by ring, Real.rpow_neg hD0.le]
  -- the main term
  have hmain : |(N : ℝ) * V D - A * N| ≤ N * (K₁ * (D : ℝ) ^ (θ - 1)) := by
    rw [show (N : ℝ) * V D - A * N = N * (V D - A) by ring, abs_mul, abs_of_pos hN0]
    exact mul_le_mul_of_nonneg_left (hVA D hD1) hN0.le
  -- the powers of `D`
  have hDpow : (D : ℝ) ^ (θ - 1) ≤ 2 ^ (1 - θ) * (N : ℝ) ^ (lam * (θ - 1)) := by
    calc (D : ℝ) ^ (θ - 1) ≤ ((N : ℝ) ^ lam / 2) ^ (θ - 1) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hDhalf (by linarith)
      _ = 2 ^ (1 - θ) * (N : ℝ) ^ (lam * (θ - 1)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN0.le,
            show θ - 1 = -(1 - θ) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul]
          ring
  have hNexp : (N : ℝ) * (N : ℝ) ^ (lam * (θ - 1)) = (N : ℝ) ^ (lam * a) := by
    rw [← hlamθ, Real.rpow_add hN0, Real.rpow_one]
  have hDa : (D : ℝ) ^ a ≤ (N : ℝ) ^ (lam * a) := by
    calc (D : ℝ) ^ a ≤ ((N : ℝ) ^ lam) ^ a := Real.rpow_le_rpow hD0.le hDle ha0.le
      _ = (N : ℝ) ^ (lam * a) := by rw [← Real.rpow_mul hN0.le]
  have hexp : a / (1 + a - θ) = lam * a := by rw [hlam]; ring
  rw [hhead, hexp]
  have hsplit3 : (N : ℝ) * V D - ∑ d ∈ Ioc 0 D, f d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) +
      ∑ d ∈ Ioc D N, f d * ((N / d : ℕ) : ℝ) - A * N =
      ((N : ℝ) * V D - A * N) - ∑ d ∈ Ioc 0 D, f d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) +
        ∑ d ∈ Ioc D N, f d * ((N / d : ℕ) : ℝ) := by ring
  rw [hsplit3]
  have htri := (abs_add_le (((N : ℝ) * V D - A * N) -
      ∑ d ∈ Ioc 0 D, f d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)))
    (∑ d ∈ Ioc D N, f d * ((N / d : ℕ) : ℝ))).trans (add_le_add (abs_sub _ _) le_rfl)
  have hP : 0 ≤ (N : ℝ) ^ (lam * (θ - 1)) := by positivity
  have hNP : 0 ≤ (N : ℝ) := hN0.le
  have hbig : (N : ℝ) * (K₁ * (D : ℝ) ^ (θ - 1)) + Z * (D : ℝ) ^ a +
      2 * C / (1 - θ) * N * (D : ℝ) ^ (θ - 1) ≤
      ((K₁ + 2 * C / (1 - θ)) * 2 ^ (1 - θ) + Z) * (N : ℝ) ^ (lam * a) := by
    have hcoef : 0 ≤ K₁ + 2 * C / (1 - θ) := add_nonneg hK₁0 (div_nonneg (by linarith) h1θ.le)
    have h1 : (N : ℝ) * (K₁ * (D : ℝ) ^ (θ - 1)) + 2 * C / (1 - θ) * N * (D : ℝ) ^ (θ - 1) =
        (K₁ + 2 * C / (1 - θ)) * (N * (D : ℝ) ^ (θ - 1)) := by ring
    have h2 : (N : ℝ) * (D : ℝ) ^ (θ - 1) ≤ 2 ^ (1 - θ) * (N : ℝ) ^ (lam * a) := by
      calc (N : ℝ) * (D : ℝ) ^ (θ - 1) ≤ N * (2 ^ (1 - θ) * (N : ℝ) ^ (lam * (θ - 1))) :=
            mul_le_mul_of_nonneg_left hDpow hNP
        _ = 2 ^ (1 - θ) * ((N : ℝ) * (N : ℝ) ^ (lam * (θ - 1))) := by ring
        _ = 2 ^ (1 - θ) * (N : ℝ) ^ (lam * a) := by rw [hNexp]
    have h3 := mul_le_mul_of_nonneg_left h2 hcoef
    have h4 := mul_le_mul_of_nonneg_left hDa hZ
    linarith
  linarith

/-! ## The twin coefficients -/

/-- For disjoint `S`, `T` an integer has at most one factorization into an `S`-number and a
`T`-number. -/
theorem freeFn_compl_mul_le_one {S T : Set ℕ} (hST : Disjoint S T) (d : ℕ) :
    (freeFn Sᶜ * freeFn Tᶜ) d ≤ 1 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  have hterm : ∀ x ∈ d.divisorsAntidiagonal, freeFn Sᶜ x.1 * freeFn Tᶜ x.2 =
      if SFree Sᶜ x.1 ∧ SFree Tᶜ x.2 then 1 else 0 := by
    intro x _
    rw [freeFn_apply, freeFn_apply]
    unfold sFreeR
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  have hcop : ∀ m n : ℕ, SFree Sᶜ m → SFree Tᶜ n → Nat.Coprime m n := by
    intro m n hm hn
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    have hpS : p ∈ S := by
      have h := hm.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.1⟩)
      simpa using h
    have hpT : p ∈ T := by
      have h := hn.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.1⟩)
      simpa using h
    exact Set.disjoint_left.mp hST hpS hpT
  have hcard : ((d.divisorsAntidiagonal).filter
      (fun x => SFree Sᶜ x.1 ∧ SFree Tᶜ x.2)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    obtain ⟨hxd, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyd, hyp⟩ := Finset.mem_filter.mp hy
    obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hxd
    obtain ⟨hy1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hyd
    have h1 : x.1 ∣ y.1 :=
      (hcop x.1 y.2 hxp.1 hyp.2).dvd_of_dvd_mul_right (Dvd.intro x.2 (hx1.trans hy1.symm))
    have h2 : y.1 ∣ x.1 :=
      (hcop y.1 x.2 hyp.1 hxp.2).dvd_of_dvd_mul_right (Dvd.intro y.2 (hy1.trans hx1.symm))
    have he1 : x.1 = y.1 := Nat.dvd_antisymm h1 h2
    have he2 : x.2 = y.2 := by
      have : x.1 * x.2 = x.1 * y.2 := by rw [hx1, he1, hy1]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hxp.1.1) this
    exact Prod.ext he1 he2
  exact_mod_cast hcard

/-- **The twin coefficients of an edit are bounded by one.** -/
theorem abs_twinCoeff_le_one {S T : Set ℕ} (hST : Disjoint S T) (d : ℕ) :
    |(mobFn S * freeFn Tᶜ) d| ≤ 1 :=
  (abs_twinCoeff_le S T d).trans (freeFn_compl_mul_le_one hST d)

theorem disjoint_minusSet_plusSet (e : ℕ → ℤ) : Disjoint (minusSet e) (plusSet e) := by
  refine Set.disjoint_left.mpr fun k h1 h2 => ?_
  simp only [minusSet, plusSet, Set.mem_setOf_eq] at h1 h2
  rw [h1] at h2
  norm_num at h2

/-- The twin coefficients `u = μ_S * 1_{T-numbers}` of the signed grouped edit. -/
def twin (α β γ : ℝ) (k₀ : ℕ) : ArithmeticFunction ℝ :=
  mobFn (minusSet (sEdit α β γ k₀)) * freeFn (plusSet (sEdit α β γ k₀))ᶜ

theorem abs_twin_le_one (α β γ : ℝ) (k₀ : ℕ) (n : ℕ) : |twin α β γ k₀ n| ≤ 1 :=
  abs_twinCoeff_le_one (disjoint_minusSet_plusSet _) n

/-- The norm count of the edit is `u * 1`. -/
theorem intCount_editSystem_eq (α β γ : ℝ) (k₀ : ℕ) (n : ℕ) :
    (intCount (editSystem (sEdit α β γ k₀)) (hasIntegerNorms_editSystem _) n : ℝ) =
      (twin α β γ k₀ * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
  have h := intCount_eq (minusSet (sEdit α β γ k₀)) (plusSet (sEdit α β γ k₀)) n
  refine h.trans ?_
  rw [freeFn_eq (minusSet (sEdit α β γ k₀)), twin]
  congr 1
  ring

/-- **The Dirichlet series of the twin coefficients is the cofactor**: `L(u, s) = M_B(s)` on
`Re s > 1`. -/
theorem LSeries_twin_eq (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) (k₀ : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => ((twin α β γ k₀ n : ℝ) : ℂ)) s = editCofactor α β γ k₀ s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  -- the zeta series of the edit system is the L-series of its norm count
  obtain ⟨A, C, -, hN⟩ := editSystem_count (e := sEdit α β γ k₀) (β := (α + 1) / 2) (by linarith)
    (by linarith) (summable_abs_sEdit_rpow hα0 hα γ k₀ (by linarith))
  have hLin := BalanceLaw.hasLinearCounting_of_count (B := editSystem (sEdit α β γ k₀)) (by linarith) hN
  have hZr := (editSystem (sEdit α β γ k₀)).summable_intNorm_rpow (isDiscrete_editSystem (sEdit α β γ k₀)) hLin hs
  obtain ⟨-, hζB⟩ := zetaSeriesC_eq_LSeries_of_summable (hasIntegerNorms_editSystem (sEdit α β γ k₀))
    (isDiscrete_editSystem (sEdit α β γ k₀)) hZr
  -- the norm count is `u ⍟ 1`
  have hconv : (fun n => (intCount (editSystem (sEdit α β γ k₀)) (hasIntegerNorms_editSystem (sEdit α β γ k₀)) n : ℂ)) =
      LSeries.convolution (fun n => ((twin α β γ k₀ n : ℝ) : ℂ)) (1 : ℕ → ℂ) := by
    funext n
    rw [LSeries.convolution_def]
    have h := intCount_editSystem_eq α β γ k₀ n
    rw [ArithmeticFunction.mul_apply] at h
    have hcast : (intCount (editSystem (sEdit α β γ k₀)) (hasIntegerNorms_editSystem (sEdit α β γ k₀)) n : ℂ) =
        (((intCount (editSystem (sEdit α β γ k₀)) (hasIntegerNorms_editSystem (sEdit α β γ k₀)) n : ℕ) : ℝ) : ℂ) :=
      (Complex.ofReal_natCast _).symm
    rw [hcast, h]
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := by
      obtain ⟨hx1, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      intro h0; rw [h0, mul_zero] at hx1; exact hn hx1.symm
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hx2]
  have hsu : LSeriesSummable (fun n => ((twin α β γ k₀ n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, sub_self, Real.rpow_zero, mul_one]
      exact abs_twin_le_one α β γ k₀ n⟩
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hLprod : (editSystem (sEdit α β γ k₀)).zetaSeriesC s =
      LSeries (fun n => ((twin α β γ k₀ n : ℝ) : ℂ)) s * riemannZeta s := by
    rw [hζB, hconv, LSeries_convolution' hsu h1, LSeries_one_eq_riemannZeta hs]
  -- and `ζ_B = ζ · M_B`
  have hfac := sub_one_mul_zetaSeriesC_eq (α := α) hβ γ k₀ hs
  rw [zetaResidueUnit_eq_of_ne hs1, hLprod] at hfac
  have hζ0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have : (s - 1) * riemannZeta s *
      (LSeries (fun n => ((twin α β γ k₀ n : ℝ) : ℂ)) s - editCofactor α β γ k₀ s) = 0 := by
    linear_combination hfac
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_ne_zero hs10 hζ0)
  · exact sub_eq_zero.mp h

/-! ## The cofactor left of the line -/

/-- The finite Euler factor of the model is bounded on `Re s ≥ σ₀` for `σ₀ > β − 1`. -/
theorem exists_norm_posFiniteFactor_le_of_re {σ₀ : ℝ} (hβσ : β - 1 < σ₀) (γ : ℝ) (k₀ : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, σ₀ ≤ s.re →
      ‖posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ ≤ B := by
  set c : ℝ := (2 : ℝ) ^ (β - 1 - σ₀) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : 0 ≤ c := by positivity
  have hinv : 0 ≤ (1 - c)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨((1 - c)⁻¹ * (1 - c)⁻¹) ^ (smallPrimes (2 ^ k₀ - 1)).card, by positivity,
    fun s hs => ?_⟩
  have hfac : ∀ z : ℂ, ‖z‖ ≤ c → ‖(1 - z)⁻¹‖ ≤ (1 - c)⁻¹ := by
    intro z hz
    rw [norm_inv]
    have h1 : 1 - c ≤ ‖1 - z‖ := by
      have := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at this
      linarith
    exact inv_anti₀ (by linarith) h1
  have hpow : ∀ q : Nat.Primes, ∀ w : ℂ, w.re ≤ β - 1 - σ₀ → ‖((q : ℕ) : ℂ) ^ w‖ ≤ c := by
    intro q w hw
    rw [Complex.norm_natCast_cpow_of_pos q.2.pos]
    have hq2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.2.two_le
    calc ((q : ℕ) : ℝ) ^ w.re ≤ (2 : ℝ) ^ w.re :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
      _ ≤ c := Real.rpow_le_rpow_of_exponent_le (by norm_num) hw
  unfold posFiniteFactor
  refine (Finset.norm_prod_le _ _).trans ?_
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hfac _ (hpow q _ (by simp [zeroPt]; linarith)))
    (hfac _ (hpow q _ (by simp [zeroPt]; linarith))) (norm_nonneg _) hinv

/-- **The model cofactor is subpolynomial on `σ₀ ≤ Re s ≤ 2`** when `ζ` has no zero right of
`Θ < σ₀ + 1 − β`. -/
theorem exists_norm_posCofactor_le_of_re (hβ0 : 0 ≤ β) (γ : ℝ) (k₀ : ℕ)
    {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {σ₀ : ℝ} (hσΘ : Θ + β - 1 < σ₀) (hσ1 : σ₀ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 →
      ‖posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ ≤ K * (2 + |s.im|) ^ ε := by
  set δ : ℝ := (σ₀ + 1 - β - Θ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  obtain ⟨Kb, hKb, -, hinv⟩ := exists_invZeta_shift_data_of_zeroFree hΘ hΘ1 hzf hδ0 hδ1
    (half_pos hε) 3
  obtain ⟨B, hB, hfin⟩ := exists_norm_posFiniteFactor_le_of_re (β := β) (σ₀ := σ₀) (by linarith) γ k₀
  refine ⟨Kb * (1 + |γ|) ^ (ε / 2) * (Kb * (1 + |γ|) ^ (ε / 2)) * B, by positivity,
    fun s hs1 hs2 => ?_⟩
  have hmem : ∀ w : ℂ, w.re = s.re + 1 - β →
      w ∈ GaloisForLFunctions.HTGeometry.verticalStrip (Θ + δ) 3 := fun w hw =>
    ⟨by rw [hw, hδ]; linarith, by rw [hw]; linarith⟩
  have hb : ∀ w : ℂ, w.re = s.re + 1 - β → |w.im| ≤ |s.im - γ| ∨ |w.im| ≤ |s.im + γ| →
      ‖invZeta w‖ ≤ Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2) := by
    intro w hw him
    refine (hinv w (hmem w hw)).trans ?_
    have hle : 2 + |w.im| ≤ (1 + |γ|) * (2 + |s.im|) := by
      rcases him with h | h
      · exact (by linarith : 2 + |w.im| ≤ 2 + |s.im - γ|).trans (two_add_abs_sub_le _ _)
      · have := two_add_abs_sub_le s.im (-γ)
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
    calc Kb * (2 + |w.im|) ^ (ε / 2) ≤ Kb * ((1 + |γ|) * (2 + |s.im|)) ^ (ε / 2) := by
          gcongr
      _ = Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have h1 := hb (s + 1 - zeroPt β γ) (by simp [zeroPt]) (Or.inl (by simp [zeroPt]))
  have h2 := hb (s + 1 - (starRingEnd ℂ) (zeroPt β γ)) (by simp [zeroPt])
    (Or.inr (by simp [zeroPt]))
  unfold posCofactor
  rw [norm_mul, norm_mul]
  calc ‖invZeta (s + 1 - zeroPt β γ)‖ * ‖invZeta (s + 1 - (starRingEnd ℂ) (zeroPt β γ))‖ *
        ‖posFiniteFactor (2 ^ k₀ - 1) (zeroPt β γ) s‖
      ≤ (Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) *
          (Kb * (1 + |γ|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) * B := by
        gcongr
        exact hfin s hs1
    _ = Kb * (1 + |γ|) ^ (ε / 2) * (Kb * (1 + |γ|) ^ (ε / 2)) * B *
          ((2 + |s.im|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) := by ring
    _ = _ := by
        rw [← Real.rpow_add (by positivity)]; ring_nf

/-- The exponent `H₁ + Q + R` grows at most like `√log` on `Re s ≥ σ₀`. -/
theorem exists_norm_editExponent_le_of_re (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {σ₀ : ℝ} (hσα : α / 2 < σ₀) (hσβ : β - 1 / 2 < σ₀) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ s : ℂ, σ₀ ≤ s.re →
      ‖editExponent α β γ k₀ s‖ ≤ C₁ * Real.sqrt (Real.log (|s.im| + 2)) + C₂ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hH⟩ := exists_norm_editSeries_le hα0 hα hβ γ hk₀ hσα
  obtain ⟨CQ, hCQ, hQ⟩ := exists_norm_editRem_le (β := β) hα0 hα γ k₀ hσα
  obtain ⟨CR, hCR, hR⟩ := exists_norm_pairRem_le β γ k₀ hσβ
  refine ⟨C₁, C₂ + CQ + CR, hC₁, by positivity, fun s hs => ?_⟩
  unfold editExponent
  have : ‖editSeries α β γ k₀ s + editRem (sEdit α β γ k₀) s + pairRem β γ k₀ s‖ ≤
      ‖editSeries α β γ k₀ s‖ + ‖editRem (sEdit α β γ k₀) s‖ + ‖pairRem β γ k₀ s‖ :=
    norm_add₃_le
  linarith [hH s hs, hQ s hs, hR s hs]

/-- **The cofactor of the edit is subpolynomial left of the line**: for
`σ₀ > max(α/2, β − ½, Θ + β − 1)` and `ε > 0`, `‖M_B(s)‖ ≤ K (2 + |Im s|)^ε` on
`σ₀ ≤ Re s ≤ 2`. -/
theorem exists_norm_editCofactor_le_of_re (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (γ : ℝ) {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {σ₀ : ℝ} (hσ : contAbscissa α β Θ < σ₀)
    (hσ1 : σ₀ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 →
      ‖editCofactor α β γ k₀ s‖ ≤ K * (2 + |s.im|) ^ ε := by
  simp only [contAbscissa, max_lt_iff] at hσ
  obtain ⟨⟨hσα, hσβ⟩, hσΘ⟩ := hσ
  obtain ⟨KM, hKM, hM⟩ := exists_norm_posCofactor_le_of_re hβ0 γ k₀ hΘ hΘ1 hzf hσΘ hσ1
    (half_pos hε)
  obtain ⟨C₁, C₂, hC₁, hC₂, hE⟩ := exists_norm_editExponent_le_of_re hα0 hα hβ γ hk₀ hσα hσβ
  refine ⟨KM * (Real.exp C₂ * Real.exp (C₁ ^ 2 / (4 * (ε / 2)))), by positivity,
    fun s hs1 hs2 => ?_⟩
  have hexp : ‖cexp (editExponent α β γ k₀ s)‖ ≤
      Real.exp C₂ * (Real.exp (C₁ ^ 2 / (4 * (ε / 2))) * (|s.im| + 2) ^ (ε / 2)) := by
    rw [Complex.norm_exp]
    calc Real.exp (editExponent α β γ k₀ s).re ≤ Real.exp ‖editExponent α β γ k₀ s‖ :=
          Real.exp_le_exp.mpr (Complex.re_le_norm _)
      _ ≤ Real.exp (C₁ * Real.sqrt (Real.log (|s.im| + 2)) + C₂) :=
          Real.exp_le_exp.mpr (hE s hs1)
      _ = Real.exp C₂ * Real.exp (C₁ * Real.sqrt (Real.log (|s.im| + 2))) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by gcongr; exact exp_mul_sqrt_log_le (half_pos hε) s.im
  unfold editCofactor
  rw [norm_mul]
  calc ‖posCofactor (2 ^ k₀ - 1) (zeroPt β γ) s‖ * ‖cexp (editExponent α β γ k₀ s)‖
      ≤ (KM * (2 + |s.im|) ^ (ε / 2)) *
          (Real.exp C₂ * (Real.exp (C₁ ^ 2 / (4 * (ε / 2))) * (|s.im| + 2) ^ (ε / 2))) :=
        mul_le_mul (hM s hs1 hs2) hexp (norm_nonneg _) (by positivity)
    _ = KM * (Real.exp C₂ * Real.exp (C₁ ^ 2 / (4 * (ε / 2)))) *
          ((2 + |s.im|) ^ (ε / 2) * (2 + |s.im|) ^ (ε / 2)) := by
        rw [add_comm (|s.im|) 2]; ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]; ring_nf

/-! ## Partial sums of the twin coefficients -/

/-- **The twin coefficients have power partial sums**: `|Σ_{0<j≤n} u(j)| ≤ C n^{(ε+σ₀)/(1+ε)+κ}`
for `σ₀ > max(α/2, β − ½, Θ + β − 1)`, by the smoothed Perron shift of `L(u, s) = M_B(s)`. -/
theorem exists_abs_sum_twin_le (hα0 : 0 < α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1) (γ : ℝ)
    {k₀ : ℕ} (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {σ₀ : ℝ} (hσ : contAbscissa α β Θ < σ₀)
    (hσ1 : σ₀ < 1) {ε κ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ j ∈ Ioc 0 n, twin α β γ k₀ j| ≤ C * (n : ℝ) ^ ((ε + σ₀) / (1 + ε) + κ) := by
  have hσ' := hσ
  simp only [contAbscissa, max_lt_iff] at hσ'
  have hσ₀0 : 0 < σ₀ := by linarith [hσ'.1.1]
  obtain ⟨K, hK0, hK⟩ := exists_norm_editCofactor_le_of_re hα0 hα hβ0 hβ γ hk₀ hΘ hΘ1 hzf hσ hσ1
    hε
  set c : ℕ → ℂ := fun n => ((twin α β γ k₀ n : ℝ) : ℂ) with hcdef
  have hc0 : c 0 = 0 := by simp [hcdef]
  have hc : ∀ n, ‖c n‖ ≤ 1 := fun n => by
    simp only [hcdef, Complex.norm_real, Real.norm_eq_abs]
    exact abs_twin_le_one α β γ k₀ n
  set H : ℂ → ℂ := fun s => (s - 1) * editCofactor α β γ k₀ s with hHdef
  have hH : DifferentiableOn ℂ H {s | contAbscissa α β Θ < s.re} :=
    (differentiableOn_id.sub_const 1).mul ((differentiableOn_editCofactor hα0 hα hβ γ hk₀ hΘ
      hzf).mono fun s hs => lt_re_of_contAbscissa_lt hs)
  have hHdiv : ∀ s : ℂ, s ≠ 1 → H s / (s - 1) = editCofactor α β γ k₀ s := fun s hs => by
    simp only [hHdef]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)
  have hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries c s := fun s hs => by
    rw [hHdiv s (fun h => by rw [h] at hs; simp at hs), LSeries_twin_eq hα0 hα hβ γ k₀ hs]
  have hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖H s / (s - 1)‖ ≤ K * 3 ^ ε * |s.im| ^ ε := by
    intro s h1 h2 h3
    have hs1 : s ≠ 1 := fun h => by rw [h] at h3; simp at h3; linarith
    rw [hHdiv s hs1]
    refine (hK s h1 (by linarith)).trans ?_
    calc K * (2 + |s.im|) ^ ε ≤ K * (3 * |s.im|) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hε.le) hK0
      _ = K * 3 ^ ε * |s.im| ^ ε := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]; ring
  have hleft : ∀ t : ℝ, ‖H (σ₀ + t * I) / (σ₀ + t * I - 1)‖ ≤ K * 2 ^ ε * (|t| + 1) ^ ε := by
    intro t
    have hs1 : (σ₀ : ℂ) + t * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [hHdiv _ hs1]
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    have him : ((σ₀ : ℂ) + t * I).im = t := by simp
    have h := hK ((σ₀ : ℂ) + t * I) (by rw [hre]) (by rw [hre]; linarith)
    rw [him] at h
    refine h.trans ?_
    calc K * (2 + |t|) ^ ε ≤ K * (2 * (|t| + 1)) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
            (by linarith [abs_nonneg t]) hε.le) hK0
      _ = K * 2 ^ ε * (|t| + 1) ^ ε := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  obtain ⟨C, hC⟩ := GaloisForLFunctions.HTGeometry.SmoothedPerron.exists_norm_sum_sub_le c hc0 hc
    (H := H) (a := contAbscissa α β Θ) (σ₀ := σ₀) hσ hσ₀0 hσ1 hH hLS (K := K * 3 ^ ε)
    (T₀ := 1) (κ₁ := ε) (by linarith) hstrip (K₀ := K * 2 ^ ε) (θ := ε) hε.le hε1 hleft
    (κ := κ) hκ
  have hH1 : H 1 = 0 := by simp [hHdef]
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h
  refine ⟨C, hC0, fun n hn => ?_⟩
  have h := hC n (by exact_mod_cast hn)
  rw [hH1, zero_mul, sub_zero, Nat.floor_natCast] at h
  have hIic : Finset.Iic n = insert 0 (Ioc 0 n) := by
    ext j; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hIic, Finset.sum_insert (by simp), hc0, zero_add] at h
  have hsum : ∑ j ∈ Ioc 0 n, c j = ((∑ j ∈ Ioc 0 n, twin α β γ k₀ j : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ## The count of the signed grouped edit -/

/-- **The signed grouped edit counts below the square root.**  With `Θ = zetaZeroAbscissa`, let
`½ < β < 2/3`, `Θ + 2β < 2` and `ζ(β + iγ) ≠ 0`.  Then for some `α` and `k₀` the signed grouped
edit with zero pair `β ± iγ` is an integer-norm fake at a count exponent `c < ½`:
`N_B(x) = A x + O(x^c)`, `A > 0`, and `(s − 1)ζ_B` continues (as `editG`) to a half-plane
`Re s > σ₁`, `σ₁ < ½`, where its zeros are exactly those of `(s − 1)ζ(s)` and `β ± iγ`. -/
theorem exists_isIntegerNormFakeAt_sEdit_lt_half {β γ : ℝ} (hβ : 1 / 2 < β) (hβ23 : β < 2 / 3)
    (hΘβ : zetaZeroAbscissa + 2 * β < 2) (hζ : riemannZeta (zeroPt β γ) ≠ 0) :
    ∃ (α : ℝ) (k₀ : ℕ) (c : ℝ), c < 1 / 2 ∧
      IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) c ∧
      (∀ s : ℂ, 1 < s.re →
        editG α β γ k₀ s = (s - 1) * (editSystem (sEdit α β γ k₀)).zetaSeriesC s) ∧
      ∃ σ₁ : ℝ, σ₁ < 1 / 2 ∧ DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | σ₁ < s.re} ∧
        ∀ s : ℂ, σ₁ < s.re → (editG α β γ k₀ s = 0 ↔
          zetaResidueUnit s = 0 ∨ s = zeroPt β γ ∨ s = (starRingEnd ℂ) (zeroPt β γ)) := by
  set Θ := zetaZeroAbscissa with hΘdef
  have hΘ : 1 / 2 ≤ Θ := half_le_zetaZeroAbscissa
  have hΘ1 : Θ ≤ 1 := zetaZeroAbscissa_le_one
  have hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 :=
    fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz
  -- parameters
  set g : ℝ := min (2 - Θ - 2 * β) (2 / 3 - β) with hg
  have hg0 : 0 < g := lt_min (by linarith) (by linarith)
  have hg1 : g ≤ 2 - Θ - 2 * β := min_le_left _ _
  have hg2 : g ≤ 2 / 3 - β := min_le_right _ _
  set α : ℝ := β + g / 10 with hαdef
  set a : ℝ := β + g / 5 with hadef
  set ε : ℝ := g / 10 with hεdef
  set κ : ℝ := g / 10 with hκdef
  set σ₀ : ℝ := max (α / 2) (Θ + β - 1) + g / 10 with hσ₀def
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β < 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := by linarith
  have hαβ : β < α := by linarith
  have hε0 : 0 < ε := by linarith
  have hε1 : ε < 1 := by linarith
  have hκ0 : 0 < κ := by linarith
  have hmax : max (α / 2) (Θ + β - 1) ≤ 1 - 8 * g / 10 - a :=
    max_le (by linarith) (by linarith)
  have hmax0 : α / 2 ≤ max (α / 2) (Θ + β - 1) := le_max_left _ _
  have hmax1 : Θ + β - 1 ≤ max (α / 2) (Θ + β - 1) := le_max_right _ _
  have haσ : a + σ₀ ≤ 1 - 7 * g / 10 := by rw [hσ₀def]; linarith
  have hσ1 : σ₀ < 1 := by linarith
  have hσ : contAbscissa α β Θ < σ₀ := by
    simp only [contAbscissa]
    refine max_lt (max_lt (by linarith) (by linarith)) (by linarith)
  have hσ₀0 : 0 < σ₀ := by linarith
  -- the block index
  obtain ⟨k₀, hk₀def⟩ : ∃ k : ℕ, k = ⌈10 / g⌉₊ := ⟨_, rfl⟩
  have hk₀ : 1 ≤ (k₀ : ℝ) * (α - β) := by
    have h1 := Nat.le_ceil (10 / g)
    rw [← hk₀def, div_le_iff₀ hg0] at h1
    have hαβ' : α - β = g / 10 := by rw [hαdef]; ring
    rw [hαβ']
    linarith
  -- partial sums of the twin coefficients
  obtain ⟨CU, hCU0, hU⟩ := exists_abs_sum_twin_le (γ := γ) hα0 hα1 hβ0 hβ1 hk₀ hΘ hΘ1 hzf hσ hσ1
    hε0 hε1 hκ0
  set θM : ℝ := (ε + σ₀) / (1 + ε) + κ with hθM
  have hθM0 : 0 ≤ θM := by rw [hθM]; positivity
  have hθMle : θM ≤ ε + σ₀ + κ := by
    rw [hθM]
    have := div_le_self (by linarith : (0 : ℝ) ≤ ε + σ₀) (by linarith : (1 : ℝ) ≤ 1 + ε)
    linarith
  have haθ : a + θM < 1 := by linarith
  have hθM1 : θM < 1 := by linarith
  have hθa : θM ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  -- the Rankin mass of the twin coefficients
  set e := sEdit α β γ k₀ with he
  have hsumm := summable_abs_sEdit_rpow (β := β) hα0 hα1 γ k₀ (θ := a) (by linarith)
  have hind : ∀ U : Set ℕ, (∀ p ∈ U, |(e p : ℝ)| = 1) →
      Summable fun p : ℕ => U.indicator (fun n => (n : ℝ) ^ (-a)) p := by
    intro U hU1
    refine Summable.of_nonneg_of_le (fun p => Set.indicator_nonneg
      (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) p) (fun p => ?_) hsumm
    by_cases hp : p ∈ U
    · rw [Set.indicator_of_mem hp, hU1 p hp, one_mul]
    · rw [Set.indicator_of_notMem hp]
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hS := hind (minusSet e) fun p hp => by
    simp only [minusSet, Set.mem_setOf_eq] at hp; rw [hp]; norm_num
  have hT := hind (plusSet e) fun p hp => by
    simp only [plusSet, Set.mem_setOf_eq] at hp; rw [hp]; norm_num
  set Z : ℝ := (∑' j : ℕ, sFreeR (minusSet e)ᶜ j * (j : ℝ) ^ (-a)) *
    ∑' j : ℕ, sFreeR (plusSet e)ᶜ j * (j : ℝ) ^ (-a) with hZ
  have hZ0 : 0 ≤ Z := mul_nonneg
    (tsum_nonneg fun j => mul_nonneg (sFreeR_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (tsum_nonneg fun j => mul_nonneg (sFreeR_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hR : ∀ n : ℕ, 1 ≤ n → ∑ j ∈ Ioc 0 n, |twin α β γ k₀ j| ≤ Z * (n : ℝ) ^ a := by
    intro n hn
    have hRank := sum_abs_twinCoeff_mul_rpow_le ha0 hS hT n
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc ∑ j ∈ Ioc 0 n, |twin α β γ k₀ j|
        ≤ ∑ j ∈ Ioc 0 n, |twin α β γ k₀ j| * (j : ℝ) ^ (-a) * (n : ℝ) ^ a := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨hj0, hjn⟩ := Finset.mem_Ioc.mp hj
          have hj0' : (0 : ℝ) < j := by exact_mod_cast hj0
          have h1 : 1 ≤ (j : ℝ) ^ (-a) * (n : ℝ) ^ a := by
            rw [Real.rpow_neg hj0'.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hj0' _)]
            exact Real.rpow_le_rpow hj0'.le (by exact_mod_cast hjn) ha0.le
          calc |twin α β γ k₀ j| = |twin α β γ k₀ j| * 1 := (mul_one _).symm
            _ ≤ |twin α β γ k₀ j| * ((j : ℝ) ^ (-a) * (n : ℝ) ^ a) :=
                mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            _ = _ := by ring
      _ = (∑ j ∈ Ioc 0 n, |twin α β γ k₀ j| * (j : ℝ) ^ (-a)) * (n : ℝ) ^ a := by
          rw [Finset.sum_mul]
      _ ≤ Z * (n : ℝ) ^ a := mul_le_mul_of_nonneg_right hRank (by positivity)
  -- the hyperbola count
  obtain ⟨A, Kh, hcount⟩ := exists_abs_sum_mul_zeta_sub_le (twin α β γ k₀) hθM0 hθM1 hθa ha0
    hCU0 hZ0 hU hR
  set c : ℝ := a / (1 + a - θM) with hcdef
  have hden : 0 < 1 + a - θM := by linarith
  have hc : c < 1 / 2 := by rw [hcdef, div_lt_iff₀ hden]; linarith
  have hc0 : 0 ≤ c := by rw [hcdef]; exact div_nonneg ha0.le hden.le
  have hKh0 : 0 ≤ Kh := by
    have h := (abs_nonneg _).trans (hcount 1 le_rfl)
    rwa [Nat.cast_one, Real.one_rpow, mul_one] at h
  have hcnt : ∀ x : ℝ, 1 ≤ x →
      |((editSystem e).countBall x : ℝ) - A * x| ≤ (Kh + |A|) * x ^ c := by
    intro x hx
    set N : ℕ := ⌊x⌋₊ with hNdef
    have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
    have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x < N + 1 := Nat.lt_floor_add_one x
    have hball : ((editSystem e).countBall x : ℝ) =
        ∑ n ∈ Ioc 0 N, (twin α β γ k₀ * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
      have h1 := countBall_eq_sum_intCount (hasIntegerNorms_editSystem e)
        (isDiscrete_editSystem e) (by linarith : (0 : ℝ) ≤ x)
      have h2 := sum_intCount_eq_countBall (hasIntegerNorms_editSystem e)
        (isDiscrete_editSystem e) N
      have h3 := countBall_eq_sum_intCount (hasIntegerNorms_editSystem e)
        (isDiscrete_editSystem e) (Nat.cast_nonneg N)
      rw [Nat.floor_natCast] at h3
      rw [h1, ← hNdef, ← h3, ← h2]
      exact Finset.sum_congr rfl fun n _ => intCount_editSystem_eq α β γ k₀ n
    rw [hball]
    have hxc : 1 ≤ x ^ c := Real.one_le_rpow hx hc0
    have hNc : (N : ℝ) ^ c ≤ x ^ c := Real.rpow_le_rpow (Nat.cast_nonneg _) hNx hc0
    have h1 := hcount N hN1
    have h2 : |A * N - A * x| ≤ |A| := by
      rw [← mul_sub, abs_mul]
      have : |(N : ℝ) - x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact mul_le_of_le_one_right (abs_nonneg _) this
    calc |∑ n ∈ Ioc 0 N, (twin α β γ k₀ * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n -
          A * x|
        ≤ |∑ n ∈ Ioc 0 N, (twin α β γ k₀ * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n -
            A * N| + |A * N - A * x| := abs_sub_le _ _ _
      _ ≤ Kh * (N : ℝ) ^ c + |A| := add_le_add h1 h2
      _ ≤ Kh * x ^ c + |A| * x ^ c :=
          add_le_add (mul_le_mul_of_nonneg_left hNc hKh0) (le_mul_of_one_le_right (abs_nonneg _) hxc)
      _ = (Kh + |A|) * x ^ c := by ring
  -- the fake, and the positive density
  have hΘβ' : Θ + β < 3 / 2 := by linarith
  have hfake := isIntegerNormFakeAt_editSystem_sEdit hα0 hα1 hβ hβ1 γ hk₀ hΘ hzf hΘβ' hζ
    (β_c := (α + 1) / 2) (by linarith) (by linarith)
  have hcntc : ∀ x : ℝ, 1 ≤ x →
      |((editSystem e).countBall x : ℝ) - A * x| ≤ (Kh + |A|) * x ^ ((α + 1) / 2) := by
    intro x hx
    refine (hcnt x hx).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (add_nonneg hKh0 (abs_nonneg A)))
  have hApos := pos_density_of_integerNormFakeAt_lt_one hfake (by linarith) hcntc
  obtain ⟨h1, h2, h3, -, h5⟩ := hfake
  refine ⟨α, k₀, c, hc, ⟨h1, h2, h3, ⟨A, Kh + |A|, hApos.le, hcnt⟩, h5⟩,
    fun s hs => editG_eq hβ1 γ k₀ hs, contAbscissa α β Θ,
    contAbscissa_lt_half hα1 hβ1 hΘβ', differentiableOn_editG hα0 hα1 hβ1 γ hk₀ hΘ hzf,
    fun s hs => editG_eq_zero_iff γ k₀ hzf hs⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
