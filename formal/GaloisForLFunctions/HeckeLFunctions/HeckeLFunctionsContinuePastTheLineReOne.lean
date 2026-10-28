import GaloisForLFunctions.HeckeLFunctions.IdealsAreEquidistributedInRayClasses
import GaloisForLFunctions.HTGeometry.DirichletSeriesBoundedPartialSums

/-!
# Hecke L-functions continue past the line `Re s = 1`

Write `α = 1 − 1/n`, `n = [K : ℚ]`.

* **Dirichlet series with partial sums `O(x^θ)`** (`growthCont`): if `c(0) = 0` and
  `‖Σ_{k ≤ x} c(k)‖ ≤ K x^θ` for `x ≥ 1`, then for real `σ > θ` the twisted sums
  `Σ_{k<N} c(k) k^{−σ}` are bounded (summation by parts, `exists_norm_sum_term_le`), so the partial
  sums of `Σ c(k) k^{−s}` converge on `Re s > θ` to a holomorphic function
  (`tendsto_sum_term_growthCont`, `differentiableOn_growthCont`) which equals the L-series where it
  converges absolutely (`growthCont_eq_LSeries`) and is bounded on every real ray `σ ≥ σ₀ > θ`
  (`exists_norm_growthCont_le`).
* **Nontrivial characters**: for `ψ ≠ 1` the partial sums of `ψ` are `O(x^α)`, so `L(s, ψ)`
  continues holomorphically to `Re s > α` (`heckeLCont`) and stays bounded as `s → 1⁺`
  (`exists_norm_heckeL_le`).
* **The trivial character**: with `ρ_𝔪 = h_𝔪 κ_𝔪` the partial sums of `1` are `ρ_𝔪 x + O(x^α)`, so
  `L(s, 1) = ρ_𝔪 ζ(s) + R(s)` with `R` holomorphic on `Re s > α` (`heckeL_one_eq`), and
  `(s − 1) L(s, 1) → ρ_𝔪` as `s → 1⁺` (`tendsto_sub_one_mul_heckeL_one`).
-/

noncomputable section

open Filter Topology Complex NumberField Module Finset
open scoped Classical

namespace GaloisForLFunctions.HeckeLFunctions

open GaloisForLFunctions.HTGeometry.BoundedPartialSums

section Growth

variable {c : ℕ → ℂ} {θ K : ℝ}

/-- `Σ_{k<N+1} c(k) = Σ_{k ∈ [1,N]} c(k)` when `c(0) = 0`. -/
theorem sum_range_succ_eq_sum_Icc (hc0 : c 0 = 0) (N : ℕ) :
    ∑ k ∈ range (N + 1), c k = ∑ k ∈ Icc 1 N, c k := by
  rw [sum_range_eq_add_Ico c N.succ_pos, hc0, zero_add, Ico_add_one_right_eq_Icc]

theorem term_eq_mul_powNeg_of_zero (hc0 : c 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term c s n = c n * powNeg s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hc0]
  · rw [LSeries.term_of_ne_zero hn, powNeg, cpow_neg, div_eq_mul_inv]

/-- **Bounded twisted partial sums**: from `‖Σ_{k ≤ x} c(k)‖ ≤ K x^θ`, the sums
`Σ_{k<N} c(k) k^{−σ}` are bounded for real `σ > θ`. -/
theorem exists_norm_sum_term_le (hc0 : c 0 = 0) (hθ : 0 ≤ θ)
    (hK : ∀ x : ℝ, 1 ≤ x → ‖∑ k ∈ Icc 1 ⌊x⌋₊, c k‖ ≤ K * x ^ θ) {σ : ℝ} (hσ : θ < σ) :
    ∃ M : ℝ, ∀ N, ‖∑ n ∈ range N, LSeries.term c σ n‖ ≤ M := by
  have hK0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hK 1 le_rfl)
  refine ⟨K * (1 + ‖(σ : ℂ)‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - (σ : ℂ).re - 1)), fun N => ?_⟩
  simp_rw [term_eq_mul_powNeg_of_zero hc0]
  refine norm_sum_mul_powNeg_le_of_growth hθ hK0 hc0 (fun n hn => ?_) (by simpa using hσ) N
  rw [partialSum, sum_range_succ_eq_sum_Icc hc0]
  simpa using hK n (by exact_mod_cast hn)

variable (c θ) in
/-- The continuation of `Σ c(k) k^{−s}` to `Re s > θ`: the limit of the partial sums, taken from
the base point `(θ + Re s)/2`. -/
def growthCont (s : ℂ) : ℂ := contLSeries c (((θ + s.re) / 2 : ℝ) : ℂ) s

variable (hc0 : c 0 = 0) (hθ : 0 ≤ θ)
  (hK : ∀ x : ℝ, 1 ≤ x → ‖∑ k ∈ Icc 1 ⌊x⌋₊, c k‖ ≤ K * x ^ θ)
include hc0 hθ hK

/-- The partial sums converge to `growthCont` on `Re s > θ`. -/
theorem tendsto_sum_term_growthCont {s : ℂ} (hs : θ < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, LSeries.term c s n) atTop (𝓝 (growthCont c θ s)) := by
  obtain ⟨M, hM⟩ := exists_norm_sum_term_le hc0 hθ hK (σ := (θ + s.re) / 2) (by linarith)
  exact tendsto_sum_term_contLSeries hM (by simp only [ofReal_re]; linarith)

/-- `growthCont` agrees with the continuation from any base point `σ₀ > θ` right of it. -/
theorem growthCont_eq_contLSeries {σ₀ : ℝ} (hσ₀ : θ < σ₀) {M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c σ₀ n‖ ≤ M) {s : ℂ} (hs : σ₀ < s.re) :
    growthCont c θ s = contLSeries c σ₀ s :=
  tendsto_nhds_unique (tendsto_sum_term_growthCont hc0 hθ hK (by linarith))
    (tendsto_sum_term_contLSeries hM (by simpa using hs))

/-- `growthCont` is holomorphic on `Re s > θ`. -/
theorem differentiableOn_growthCont : DifferentiableOn ℂ (growthCont c θ) {s | θ < s.re} := by
  intro s hs
  have hs' : θ < s.re := hs
  have hσ₀ : θ < (θ + s.re) / 2 := by linarith
  obtain ⟨M, hM⟩ := exists_norm_sum_term_le hc0 hθ hK hσ₀
  have hU : {z : ℂ | (((θ + s.re) / 2 : ℝ) : ℂ).re < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp only [Set.mem_setOf_eq,
      ofReal_re]; linarith)
  refine (((differentiableOn_contLSeries hM).differentiableAt hU).congr_of_eventuallyEq ?_
    ).differentiableWithinAt
  filter_upwards [hU] with z hz
  exact growthCont_eq_contLSeries hc0 hθ hK hσ₀ hM (by simpa using hz)

/-- `growthCont` is the L-series where the latter converges absolutely. -/
theorem growthCont_eq_LSeries {s : ℂ} (hs : θ < s.re) (hsum : LSeriesSummable c s) :
    growthCont c θ s = LSeries c s :=
  tendsto_nhds_unique (tendsto_sum_term_growthCont hc0 hθ hK hs) hsum.hasSum.tendsto_sum_nat

/-- `growthCont` is bounded on every real ray `σ > σ₀` with `σ₀ > θ`. -/
theorem exists_norm_growthCont_le {σ₀ : ℝ} (hσ₀ : θ < σ₀) :
    ∃ B : ℝ, ∀ σ : ℝ, σ₀ < σ → ‖growthCont c θ σ‖ ≤ B := by
  obtain ⟨M, hM⟩ := exists_norm_sum_term_le hc0 hθ hK hσ₀
  refine ⟨3 * M, fun σ hσ => ?_⟩
  have h := norm_contLSeries_add_ofReal_le hM (b := σ - σ₀) (by linarith)
  rwa [← ofReal_add, add_sub_cancel, ← growthCont_eq_contLSeries hc0 hθ hK hσ₀ hM
    (by simpa using hσ)] at h

end Growth

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

local notation "α" => (1 - (finrank ℚ K : ℝ)⁻¹)

theorem errExp_nonneg : 0 ≤ α :=
  sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast finrank_pos))

theorem errExp_lt_one : α < 1 :=
  sub_lt_self _ (inv_pos.mpr (by exact_mod_cast finrank_pos))

theorem heckeCoeff_zero (ψ : HeckeCharacter 𝔪) : heckeCoeff 𝔪 ψ 0 = 0 := by
  refine Finset.sum_eq_zero fun I hI => heckeValue_of_not_mem 𝔪 ψ ?_
  rintro ⟨h, -⟩
  rw [mem_idealsOfNorm] at hI
  exact h (Ideal.absNorm_eq_zero_iff.mp hI)

section Nontrivial

variable (𝔪) in
/-- The continuation of `L(s, ψ)` to `Re s > 1 − 1/n`. -/
def heckeLCont (ψ : HeckeCharacter 𝔪) : ℂ → ℂ := growthCont (heckeCoeff 𝔪 ψ) α

variable {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
include hψ

/-- **Convergence on `Re s > 1 − 1/n`**: for `ψ ≠ 1` the partial sums of `L(s, ψ)` converge. -/
theorem tendsto_sum_term_heckeLCont {s : ℂ} (hs : α < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, LSeries.term (heckeCoeff 𝔪 ψ) s n) atTop
      (𝓝 (heckeLCont 𝔪 ψ s)) := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  exact tendsto_sum_term_growthCont (heckeCoeff_zero ψ) errExp_nonneg hC hs

/-- **`L(s, ψ)` continues holomorphically to `Re s > 1 − 1/n`** for `ψ ≠ 1`. -/
theorem differentiableOn_heckeLCont :
    DifferentiableOn ℂ (heckeLCont 𝔪 ψ) {s | α < s.re} := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  exact differentiableOn_growthCont (heckeCoeff_zero ψ) errExp_nonneg hC

theorem heckeLCont_eq_heckeL {s : ℂ} (hs : 1 < s.re) : heckeLCont 𝔪 ψ s = heckeL 𝔪 ψ s := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  exact growthCont_eq_LSeries (heckeCoeff_zero ψ) errExp_nonneg hC
    (by linarith [errExp_lt_one (K := K)]) (lSeriesSummable_heckeCoeff 𝔪 ψ hs)

/-- **`L(s, ψ)` stays bounded as `s → 1⁺`** for `ψ ≠ 1`. -/
theorem exists_norm_heckeL_le : ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → ‖heckeL 𝔪 ψ σ‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  obtain ⟨B, hB⟩ := exists_norm_growthCont_le (heckeCoeff_zero ψ) errExp_nonneg hC
    (errExp_lt_one (K := K))
  refine ⟨B, fun σ hσ => ?_⟩
  rw [← heckeLCont_eq_heckeL hψ (by simpa using hσ)]
  exact hB σ hσ

end Nontrivial

section Trivial

variable (𝔪) in
/-- The density `ρ_𝔪 = h_𝔪 κ_𝔪` of all integral ideals prime to `𝔪`. -/
def heckeDensity : ℝ := Nat.card (RayClassGroup 𝔪) * rayDensity 𝔪

variable (𝔪) in
/-- **The ideals prime to `𝔪`**: `Σ_{k ≤ x} a_1(k) = ρ_𝔪 x + O(x^{1−1/n})`. -/
theorem exists_norm_sum_heckeCoeff_one_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ k ∈ Icc 1 ⌊x⌋₊, heckeCoeff 𝔪 1 k - (heckeDensity 𝔪 : ℂ) * x‖ ≤ C * x ^ α := by
  have : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _
  obtain ⟨C, hC⟩ := exists_abs_ncard_rayClassIdeals_sub_le 𝔪
  refine ⟨Fintype.card (RayClassGroup 𝔪) * C, fun x hx => ?_⟩
  rw [sum_heckeCoeff_eq, heckeDensity, Nat.card_eq_fintype_card]
  have hsplit : ∑ c, ((1 : HeckeCharacter 𝔪) c : ℂ) * (rayClassIdeals 𝔪 c x).ncard -
      ((Fintype.card (RayClassGroup 𝔪) * rayDensity 𝔪 : ℝ) : ℂ) * x =
      ∑ c : RayClassGroup 𝔪, ((((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ) : ℂ) := by
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsplit]
  calc ‖∑ c : RayClassGroup 𝔪, ((((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ) : ℂ)‖
      ≤ ∑ c : RayClassGroup 𝔪, ‖((((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : RayClassGroup 𝔪, C * x ^ α :=
        Finset.sum_le_sum fun c _ => by rw [norm_real, Real.norm_eq_abs]; exact hC c x hx
    _ = Fintype.card (RayClassGroup 𝔪) * C * x ^ α := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

variable (𝔪) in
/-- The coefficients `a_1(k) − ρ_𝔪` of `L(s, 1) − ρ_𝔪 ζ(s)`. -/
def trivialRemainder (k : ℕ) : ℂ := if k = 0 then 0 else heckeCoeff 𝔪 1 k - heckeDensity 𝔪

theorem exists_norm_sum_trivialRemainder_le :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖∑ k ∈ Icc 1 ⌊x⌋₊, trivialRemainder 𝔪 k‖ ≤ C * x ^ α := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_one_sub_le 𝔪
  refine ⟨C + |heckeDensity 𝔪|, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hxα : 1 ≤ x ^ α := Real.one_le_rpow hx errExp_nonneg
  have hsum : ∑ k ∈ Icc 1 ⌊x⌋₊, trivialRemainder 𝔪 k =
      (∑ k ∈ Icc 1 ⌊x⌋₊, heckeCoeff 𝔪 1 k - (heckeDensity 𝔪 : ℂ) * x) +
        (heckeDensity 𝔪 : ℂ) * ((x - ⌊x⌋₊ : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun k hk => if_neg (by simp at hk; omega), Finset.sum_sub_distrib,
      Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum]
  have hfl : |x - ⌊x⌋₊| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [Nat.floor_le hx0])]
    linarith [Nat.lt_floor_add_one x]
  calc _ ≤ ‖∑ k ∈ Icc 1 ⌊x⌋₊, heckeCoeff 𝔪 1 k - (heckeDensity 𝔪 : ℂ) * x‖ +
        ‖(heckeDensity 𝔪 : ℂ) * ((x - ⌊x⌋₊ : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ C * x ^ α + |heckeDensity 𝔪| * x ^ α := by
        refine add_le_add (hC x hx) ?_
        rw [← ofReal_mul, norm_real, Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) hfl).trans
          (le_mul_of_one_le_right (abs_nonneg _) hxα)
    _ = (C + |heckeDensity 𝔪|) * x ^ α := by ring

/-- **The trivial character**: `L(s, 1) = ρ_𝔪 ζ(s) + R(s)` on `Re s > 1`, with
`R = growthCont (a_1 − ρ_𝔪)`. -/
theorem heckeL_one_eq {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 1 s = heckeDensity 𝔪 * riemannZeta s + growthCont (trivialRemainder 𝔪) α s := by
  obtain ⟨C, hC⟩ := exists_norm_sum_trivialRemainder_le (𝔪 := 𝔪)
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hcoeff : ∀ {n : ℕ}, n ≠ 0 → heckeCoeff 𝔪 1 n =
      (trivialRemainder 𝔪 + (heckeDensity 𝔪 : ℂ) • (1 : ℕ → ℂ)) n := by
    intro n hn
    simp [trivialRemainder, hn]
  have hR : LSeriesSummable (trivialRemainder 𝔪) s := by
    have h := (lSeriesSummable_heckeCoeff 𝔪 1 hs).sub (h1.smul (heckeDensity 𝔪 : ℂ))
    refine (LSeriesSummable_congr s fun {n} hn => ?_).mp h
    simp [trivialRemainder, hn]
  rw [heckeL, LSeries_congr hcoeff, LSeries_add hR (h1.smul _), LSeries_smul,
    LSeries_one_eq_riemannZeta hs, growthCont_eq_LSeries (by simp [trivialRemainder])
      errExp_nonneg hC (by linarith [errExp_lt_one (K := K)]) hR, add_comm]

/-- `R(s)` is holomorphic on `Re s > 1 − 1/n`: `L(s, 1) − ρ_𝔪 ζ(s)` continues there. -/
theorem differentiableOn_growthCont_trivialRemainder :
    DifferentiableOn ℂ (growthCont (trivialRemainder 𝔪) α) {s | α < s.re} := by
  obtain ⟨C, hC⟩ := exists_norm_sum_trivialRemainder_le (𝔪 := 𝔪)
  exact differentiableOn_growthCont (by simp [trivialRemainder]) errExp_nonneg hC

/-- **The pole at `s = 1`**: `(s − 1) L(s, 1) → ρ_𝔪 = h_𝔪 κ_𝔪` as `s → 1⁺`. -/
theorem tendsto_sub_one_mul_heckeL_one :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * heckeL 𝔪 1 s) (𝓝[>] 1) (𝓝 (heckeDensity 𝔪 : ℂ)) := by
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_one_sub_le 𝔪
  have hn : (0 : ℝ) < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast finrank_pos)
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div ?_
    fun σ hσ => lSeriesSummable_heckeCoeff 𝔪 1 (by simpa using hσ)
  have hdec : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(finrank ℚ K : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_rpow_neg_atTop hn).comp tendsto_natCast_atTop_atTop).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdec
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h := hC n (by exact_mod_cast hn1)
  rw [Nat.floor_natCast] at h
  rw [show (∑ k ∈ Icc 1 n, heckeCoeff 𝔪 1 k) / (n : ℂ) - heckeDensity 𝔪 =
      (∑ k ∈ Icc 1 n, heckeCoeff 𝔪 1 k - (heckeDensity 𝔪 : ℂ) * ((n : ℝ) : ℂ)) / ((n : ℝ) : ℂ) by
    have : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast at this ⊢
    field_simp, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hn0, div_le_iff₀ hn0,
    show -(finrank ℚ K : ℝ)⁻¹ = α - 1 by ring, Real.rpow_sub_one hn0.ne', mul_div_assoc',
    div_mul_cancel₀ _ hn0.ne']
  exact h

end Trivial

end GaloisForLFunctions.HeckeLFunctions
