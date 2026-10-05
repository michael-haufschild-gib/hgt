import GaloisForLFunctions.HTGeometry.PoissonDustCompactification
import GaloisForLFunctions.HTGeometry.BanachLogSeries

/-!
# Formation cumulants: exact dust separation

For a decorated formation `F(z) = Exp_⋆(zγ) ⋆ Π_j (δ_1 + zα_j)` with `Σ_j ‖α_j‖ = S < ∞` and
`‖z‖ S < 1`, the convolution logarithm is

`log_⋆ F(z) = zγ + Σ_j log_⋆(δ_1 + zα_j) = z(γ + Σ_j α_j) + Σ_{r≥2} (-1)^{r+1} z^r/r Σ_j α_j^{⋆r}`,

with absolutely convergent coefficient sums, and `Exp_⋆` of it is `F(z)`.  The coefficients are
determined by the formation alone: two logarithms of the same formation differ by an element `c`
with `Exp_⋆ c = δ_1` and `c → 0` as `z → 0`, hence agree near `0`, and power-series coefficients
are unique.  Thus the first cumulant `C_1 = γ + Σ_j α_j` is the conserved total infinitesimal
formation, and for `r ≥ 2` the cumulant `C_r = (-1)^{r+1}/r Σ_j α_j^{⋆r}` does not see the dust.
-/

open Filter Topology NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

attribute [local instance] ratAlgebra

/-- The formation cumulants `C_0 = 0`, `C_1 = γ + Σ_j α_j` and, for `r ≥ 2`,
`C_r = (-1)^{r+1}/r Σ_j α_j^{⋆r}`. -/
def cumulant (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) : ℕ → MeasureAlgebra K
  | 0 => 0
  | r + 1 => (if r = 0 then γ else 0) + logCoeff r • ∑' j, α j ^ (r + 1)

/-- The convolution logarithm `log_⋆ F(z) = zγ + Σ_j log_⋆(δ_1 + zα_j)` of a decorated
formation. -/
def formationLog (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (z : ℂ) : MeasureAlgebra K :=
  z • γ + ∑' j, logSeries (z • α j)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem cumulant_one (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) :
    cumulant γ α 1 = γ + ∑' j, α j := by
  simp [cumulant, logCoeff_zero]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- For `r ≥ 2` the cumulant is `(-1)^{r+1}/r Σ_j α_j^{⋆r}`. -/
theorem cumulant_of_two_le (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) {r : ℕ}
    (hr : 2 ≤ r) : cumulant γ α r = logCoeff (r - 1) • ∑' j, α j ^ r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  simp [cumulant, show k + 2 - 1 = k + 1 by omega]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Dust is invisible to the cumulants of degree `r ≥ 2`.** -/
theorem cumulant_dust_invariant (γ γ' : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) {r : ℕ}
    (hr : 2 ≤ r) : cumulant γ α r = cumulant γ' α r := by
  rw [cumulant_of_two_le γ α hr, cumulant_of_two_le γ' α hr]

/-! ### Convergence -/

section Convergence

variable {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖)
include hα

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_le_tsum_norm (j : ℕ) : ‖α j‖ ≤ ∑' i, ‖α i‖ :=
  hα.le_tsum j fun _ _ => norm_nonneg _

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Each power sum `Σ_j α_j^{⋆(r+1)}` converges absolutely. -/
theorem summable_norm_pow (r : ℕ) : Summable fun j => ‖α j ^ (r + 1)‖ :=
  Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => (norm_pow_le' (α j) (Nat.succ_pos r)).trans (by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_le_tsum_norm hα j) r)
        (norm_nonneg _) |>.trans_eq (mul_comm _ _)))
    (hα.mul_left ((∑' i, ‖α i‖) ^ r))

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_smul_lt_one {z : ℂ} (hz : ‖z‖ * ∑' i, ‖α i‖ < 1) (j : ℕ) : ‖z • α j‖ < 1 := by
  rw [norm_smul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_le_tsum_norm hα j) (norm_nonneg z)) hz

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_logSeries_smul_le {z : ℂ} (hz : ‖z‖ * ∑' i, ‖α i‖ < 1) (j : ℕ) :
    ‖logSeries (z • α j)‖ ≤ ‖z‖ * ‖α j‖ / (1 - ‖z‖ * ∑' i, ‖α i‖) := by
  refine (norm_logSeries_le (norm_smul_lt_one hα hz j)).trans ?_
  rw [norm_smul]
  have h1 : ‖z‖ * ‖α j‖ ≤ ‖z‖ * ∑' i, ‖α i‖ :=
    mul_le_mul_of_nonneg_left (norm_le_tsum_norm hα j) (norm_nonneg z)
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem summable_logSeries_smul {z : ℂ} (hz : ‖z‖ * ∑' i, ‖α i‖ < 1) :
    Summable fun j => logSeries (z • α j) :=
  Summable.of_norm_bounded ((hα.mul_left ‖z‖).div_const _) (norm_logSeries_smul_le hα hz)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `Exp_⋆(log_⋆ F(z)) = F(z)` for `‖z‖ Σ_j ‖α_j‖ < 1`. -/
theorem exp_formationLog (γ : MeasureAlgebra K) {z : ℂ} (hz : ‖z‖ * ∑' i, ‖α i‖ < 1) :
    exp (formationLog γ α z) = decorated γ α z := by
  have hs := summable_logSeries_smul hα hz
  have hprod : HasProd (fun j => exp (logSeries (z • α j))) (exp (∑' j, logSeries (z • α j))) := by
    have h := ((exp_continuous (𝔸 := MeasureAlgebra K)).tendsto _).comp hs.hasSum
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, exp_sum]
  rw [formationLog, exp_add, decorated, hprod.tprod_eq.symm]
  congr 1
  exact tprod_congr fun j => exp_logSeries (norm_smul_lt_one hα hz j)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `log_⋆ F(z) = Σ_r z^r C_r` for `‖z‖ Σ_j ‖α_j‖ < 1`, with the
cumulants `C_1 = γ + Σ_j α_j` and `C_r = (-1)^{r+1}/r Σ_j α_j^{⋆r}`. -/
theorem hasSum_cumulant (γ : MeasureAlgebra K) {z : ℂ} (hz : ‖z‖ * ∑' i, ‖α i‖ < 1) :
    HasSum (fun r => z ^ r • cumulant γ α r) (formationLog γ α z) := by
  set S := ∑' i, ‖α i‖
  set q := ‖z‖ * S
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg z) (tsum_nonneg fun i => norm_nonneg _)
  set f : ℕ → ℕ → MeasureAlgebra K := fun r j => logCoeff r • (z • α j) ^ (r + 1)
  have hbound : ∀ p : ℕ × ℕ, ‖f p.1 p.2‖ ≤ q ^ p.1 * (‖z‖ * ‖α p.2‖) := fun ⟨r, j⟩ => by
    refine (norm_logSeries_term_le _ r).trans ?_
    rw [norm_smul, pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (norm_le_tsum_norm hα j) (norm_nonneg z)) r) (by positivity)
  have hT : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hz).mul_of_nonneg
      (hα.mul_left ‖z‖) (fun r => by positivity) fun j => by positivity) hbound
  set U : ℕ → MeasureAlgebra K := fun r => ∑' j, f r j
  have hU : HasSum U (∑' j, logSeries (z • α j)) := by
    have h := hT.hasSum.prod_fiberwise fun r => (hT.prod_factor r).hasSum
    rw [hT.tsum_prod] at h
    simp only [Function.uncurry_apply_pair] at h
    rw [← hT.tsum_comm] at h
    exact h
  have hUr : ∀ r, U r = z ^ (r + 1) • (logCoeff r • ∑' j, α j ^ (r + 1)) := fun r => by
    have hpow := (summable_norm_pow hα r).of_norm
    simp only [U, f, smul_pow, smul_smul]
    rw [hpow.tsum_const_smul, mul_comm, ← smul_smul]
  have hshift : HasSum (fun r => z ^ (r + 1) • cumulant γ α (r + 1))
      (z • γ + ∑' j, logSeries (z • α j)) := by
    refine ((hasSum_ite_eq 0 (z • γ)).add hU).congr_fun fun r => ?_
    rw [hUr, cumulant, smul_add]
    split_ifs with h
    · subst h; simp
    · simp
  have := (hasSum_nat_add_iff (f := fun r => z ^ r • cumulant γ α r) 1).1 hshift
  have h0 : cumulant γ α 0 = 0 := rfl
  rw [Finset.sum_range_one, h0, smul_zero, add_zero] at this
  exact this

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `‖log_⋆ F(z)‖ ≤ ‖z‖ (‖γ‖ + 2 Σ_j ‖α_j‖)` for `2‖z‖ Σ_j ‖α_j‖ ≤ 1`. -/
theorem norm_formationLog_le (γ : MeasureAlgebra K) {z : ℂ} (hz : 2 * (‖z‖ * ∑' i, ‖α i‖) ≤ 1) :
    ‖formationLog γ α z‖ ≤ ‖z‖ * (‖γ‖ + 2 * ∑' i, ‖α i‖) := by
  have hz' : ‖z‖ * ∑' i, ‖α i‖ < 1 := by linarith
  have hden : 1 / 2 ≤ 1 - ‖z‖ * ∑' i, ‖α i‖ := by linarith
  have hsum := hα.mul_left (‖z‖ * 2)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, mul_add]
  refine add_le_add le_rfl ?_
  calc ‖∑' j, logSeries (z • α j)‖ ≤ ∑' j, ‖z‖ * 2 * ‖α j‖ :=
        tsum_of_norm_bounded hsum.hasSum fun j => (norm_logSeries_smul_le hα hz' j).trans (by
          rw [div_le_iff₀ (by linarith)]
          have := mul_le_mul_of_nonneg_left hden
            (by positivity : (0 : ℝ) ≤ ‖z‖ * 2 * ‖α j‖)
          linarith)
    _ = ‖z‖ * (2 * ∑' i, ‖α i‖) := by rw [tsum_mul_left]; ring

end Convergence

/-! ### The cumulants are determined by the formation -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **The cumulants are intrinsic to the formation.**  If two decorated formations agree on a
neighbourhood of `0`, their cumulants agree in every degree. -/
theorem cumulant_eq_of_decorated_eq {γ γ' : MeasureAlgebra K} {α α' : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) (hα' : Summable fun j => ‖α' j‖) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, ‖z‖ < ρ → decorated γ α z = decorated γ' α' z) :
    cumulant γ α = cumulant γ' α' := by
  have hS : 0 ≤ ∑' i, ‖α i‖ := tsum_nonneg fun i => norm_nonneg _
  have hS' : 0 ≤ ∑' i, ‖α' i‖ := tsum_nonneg fun i => norm_nonneg _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖γ‖ + 2 * ∑' i, ‖α i‖ + (‖γ'‖ + 2 * ∑' i, ‖α' i‖) + 1 :=
    ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by linarith [norm_nonneg γ, norm_nonneg γ']
  set ρ₁ := min ρ (1 / (2 * A))
  have hρ₁ : 0 < ρ₁ := lt_min hρ (by positivity)
  have hzA : ∀ z : ℂ, ‖z‖ < ρ₁ → ‖z‖ * A ≤ 1 / 2 := fun z hz => by
    have : ‖z‖ ≤ 1 / (2 * A) := hz.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hzS : ∀ z : ℂ, ‖z‖ < ρ₁ → 2 * (‖z‖ * ∑' i, ‖α i‖) ≤ 1 := fun z hz => by
    have h1 := hzA z hz
    have h2 : ‖z‖ * (2 * ∑' i, ‖α i‖) ≤ ‖z‖ * A :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg γ, norm_nonneg γ']) (norm_nonneg z)
    linarith
  have hzS' : ∀ z : ℂ, ‖z‖ < ρ₁ → 2 * (‖z‖ * ∑' i, ‖α' i‖) ≤ 1 := fun z hz => by
    have h1 := hzA z hz
    have h2 : ‖z‖ * (2 * ∑' i, ‖α' i‖) ≤ ‖z‖ * A :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg γ, norm_nonneg γ']) (norm_nonneg z)
    linarith
  refine eq_of_hasSum_pow_smul hρ₁ (f := formationLog γ α) (fun z hz => ?_) fun z hz => ?_
  · exact hasSum_cumulant hα γ (by linarith [hzS z hz])
  · have heq : formationLog γ' α' z = formationLog γ α z := by
      have hexp : exp (formationLog γ' α' z - formationLog γ α z) = 1 := by
        rw [sub_eq_add_neg, exp_add, exp_formationLog hα' γ' (by linarith [hzS' z hz]),
          ← h z (hz.trans_le (min_le_left _ _)), ← exp_formationLog hα γ (by linarith [hzS z hz]),
          ← exp_add, add_neg_cancel, exp_zero]
      have hc : ‖formationLog γ' α' z - formationLog γ α z‖ ≤ 1 / 2 := by
        refine (norm_sub_le _ _).trans ?_
        have h1 := norm_formationLog_le hα' γ' (hzS' z hz)
        have h2 := norm_formationLog_le hα γ (hzS z hz)
        have h3 := hzA z hz
        have h4 : ‖z‖ * (‖γ'‖ + 2 * ∑' i, ‖α' i‖) + ‖z‖ * (‖γ‖ + 2 * ∑' i, ‖α i‖) ≤ ‖z‖ * A := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg z)
        linarith
      have hlt : ‖formationLog γ' α' z - formationLog γ α z‖ *
          Real.exp ‖formationLog γ' α' z - formationLog γ α z‖ < 1 := by
        have he : Real.exp ‖formationLog γ' α' z - formationLog γ α z‖ < 2 :=
          lt_of_le_of_lt (Real.exp_le_exp.2 hc) (by
            have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
            norm_num at this ⊢
            linarith)
        have h0 := norm_nonneg (formationLog γ' α' z - formationLog γ α z)
        calc ‖formationLog γ' α' z - formationLog γ α z‖ *
              Real.exp ‖formationLog γ' α' z - formationLog γ α z‖
            ≤ 1 / 2 * Real.exp ‖formationLog γ' α' z - formationLog γ α z‖ :=
              mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
          _ < 1 / 2 * 2 := by linarith
          _ = 1 := by norm_num
      exact sub_eq_zero.1 (eq_zero_of_exp_eq_one hexp hlt)
    rw [← heq]
    exact hasSum_cumulant hα' γ' (by linarith [hzS' z hz])

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Exact dust separation.**  A decorated formation determines its first cumulant
`γ + Σ_j α_j` and all atomic power sums `Σ_j α_j^{⋆r}`, `r ≥ 2`. -/
theorem total_and_powerSums_eq_of_decorated_eq {γ γ' : MeasureAlgebra K}
    {α α' : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖)
    (hα' : Summable fun j => ‖α' j‖) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, ‖z‖ < ρ → decorated γ α z = decorated γ' α' z) :
    γ + ∑' j, α j = γ' + ∑' j, α' j ∧ ∀ r, 2 ≤ r → ∑' j, α j ^ r = ∑' j, α' j ^ r := by
  have hc := cumulant_eq_of_decorated_eq hα hα' hρ h
  refine ⟨by rw [← cumulant_one, ← cumulant_one, hc], fun r hr => ?_⟩
  have h1 := congrFun hc r
  rw [cumulant_of_two_le γ α hr, cumulant_of_two_le γ' α' hr] at h1
  have hne : logCoeff (r - 1) ≠ 0 := by
    simp only [logCoeff, ne_eq, div_eq_zero_iff, pow_eq_zero_iff', neg_eq_zero, one_ne_zero,
      false_and, false_or]
    exact_mod_cast Nat.succ_ne_zero (r - 1)
  exact smul_right_injective _ hne h1

end GaloisForLFunctions.HTGeometry.FormationDust
