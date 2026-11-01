import GaloisForLFunctions.LatticeSectionTheory.TheBoostTransformRestoresTheEulerProduct
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The isotropic cone counts divisors

The split plane `ℤH ⊕ ℤV` with its own indefinite form `x² = 2mn` has no Gaussian count. Counted
along its positive isotropic cone `m, n ≥ 1` with the indefinite weight it gives

    C(t) = Σ_{m,n ≥ 1} e^{−2π t m n} = Σ_{N ≥ 1} d(N) e^{−2π t N},

the generating function of the divisor function.

* **Mellin transform** (`mellin_coneCount`). For `σ > 1`,
  `∫_0^∞ C(t) t^{σ−1} dt = Γ(σ) (2π)^{−σ} ζ(σ)²`: the split surface's own zeta function is `ζ²`,
  not an Epstein function.
* **Double pole** (`tendsto_sq_mul_coneMellin`). `(σ − 1)² Γ(σ)(2π)^{−σ}ζ(σ)² → 1/(2π)` as
  `σ → 1⁺`. Every completed function of a Gaussian Poisson pair (a weak FE-pair) has at most a
  simple pole there (`tendsto_sq_mul_Λ`), so **the isotropic count is not Poisson-dual**
  (`not_exists_FEPair_coneCount`): its duality needs a logarithmic completion, the same logarithm
  as in the pole-plane Riemann–Roch `h⁰(D) − h⁰(D^∨) = log(D²/2)`.

* **Siegel–Weil for the split plane** (`siegelWeil_splitPlane`). Averaging the definite majorant
  counts over the boost line gives the cone count: both Mellin transforms are archimedean factors
  times `ζ(σ)²`.

So the indefinite lattice has two Gaussian substitutes: its Siegel majorants (definite, fake at
large boosts, existing as a family exactly under the Hodge index) and its cone count (arithmetic,
`ζ²`, not Poisson-dual). The boost average of the first is the second.
-/

noncomputable section

open Real Complex Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.LatticeSectionTheory

/-! ### The cone count -/

/-- The weight `2π m n` of the cone point `(m, n) = (i.1 + 1, i.2 + 1)`. -/
def coneWeight (i : ℕ × ℕ) : ℝ := 2 * π * (((i.1 : ℝ) + 1) * ((i.2 : ℝ) + 1))

theorem coneWeight_pos (i : ℕ × ℕ) : 0 < coneWeight i := by
  unfold coneWeight; positivity

/-- **The isotropic count** `C(t) = Σ_{m,n ≥ 1} e^{−2π t m n}`. -/
def coneCount (t : ℝ) : ℝ := ∑' i : ℕ × ℕ, Real.exp (-coneWeight i * t)

theorem summable_coneCount {t : ℝ} (ht : 0 < t) :
    Summable fun i : ℕ × ℕ => Real.exp (-coneWeight i * t) := by
  -- `m n ≥ (m + n)/2` for `m, n ≥ 1`, so the terms are dominated by a product of geometric series
  have hg : Summable fun m : ℕ => Real.exp (-(π * t) * ((m : ℝ) + 1)) := by
    refine ((summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos] : -(π * t) < 0))).mul_left
      (Real.exp (-(π * t)))).congr fun m => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  refine (hg.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) fun i => ?_
  rw [← Real.exp_add, Real.exp_le_exp, coneWeight]
  have ha : (1 : ℝ) ≤ (i.1 : ℝ) + 1 := by linarith [(Nat.cast_nonneg i.1 : (0 : ℝ) ≤ i.1)]
  have hb : (1 : ℝ) ≤ (i.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg i.2 : (0 : ℝ) ≤ i.2)]
  have hab : ((i.1 : ℝ) + 1) + ((i.2 : ℝ) + 1) ≤ 2 * (((i.1 : ℝ) + 1) * ((i.2 : ℝ) + 1)) := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg Real.pi_pos.le ht.le)]

/-! ### The Mellin transform -/

/-- The value `Γ(σ) (2π)^{−σ} ζ(σ)²`, with `ζ(σ) = Σ_m m^{−σ}`. -/
def coneMellinValue (σ : ℝ) : ℝ :=
  Real.Gamma σ * (2 * π) ^ (-σ) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-σ)) ^ 2

theorem one_div_coneWeight_rpow (σ : ℝ) (i : ℕ × ℕ) :
    1 / coneWeight i ^ σ = (2 * π) ^ (-σ) * (((i.1 : ℝ) + 1) ^ (-σ) * ((i.2 : ℝ) + 1) ^ (-σ)) := by
  have ha : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (i.2 : ℝ) + 1 := by positivity
  rw [coneWeight, Real.mul_rpow (x := 2 * π) (by positivity) (mul_pos ha hb).le,
    Real.mul_rpow (x := (i.1 : ℝ) + 1) ha.le hb.le, Real.rpow_neg (by positivity),
    Real.rpow_neg ha.le, Real.rpow_neg hb.le, one_div, mul_inv, mul_inv]

theorem coneTerm_eq (σ : ℝ) (i : ℕ × ℕ) :
    Complex.Gamma (σ : ℂ) * 1 / ((coneWeight i : ℝ) : ℂ) ^ (σ : ℂ) =
      ((Real.Gamma σ * (2 * π) ^ (-σ) *
        (((i.1 : ℝ) + 1) ^ (-σ) * ((i.2 : ℝ) + 1) ^ (-σ)) : ℝ) : ℂ) := by
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_cpow (coneWeight_pos i).le, mul_one,
    ← Complex.ofReal_div, mul_assoc, ← one_div_coneWeight_rpow, mul_one_div]

/-- **The Mellin transform of the isotropic count** is `Γ(σ)(2π)^{−σ}ζ(σ)²` for `σ > 1`. -/
theorem mellin_coneCount {σ : ℝ} (hσ : 1 < σ) :
    mellin (fun t => (coneCount t : ℂ)) (σ : ℂ) = (coneMellinValue σ : ℂ) := by
  have hps := summable_nat_add_one_rpow hσ
  have hprod : Summable fun i : ℕ × ℕ => ((i.1 : ℝ) + 1) ^ (-σ) * ((i.2 : ℝ) + 1) ^ (-σ) :=
    hps.mul_of_nonneg hps (fun _ => Real.rpow_nonneg (by positivity) _)
      (fun _ => Real.rpow_nonneg (by positivity) _)
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : ℕ × ℕ => (1 : ℂ) * (Real.exp (-coneWeight i * t) : ℂ))
      (coneCount t : ℂ) := by
    intro t ht
    refine (Complex.hasSum_ofReal.mpr (summable_coneCount ht).hasSum).congr_fun fun i => ?_
    rw [one_mul]
  have hsum : Summable fun i : ℕ × ℕ => ‖(1 : ℂ)‖ / coneWeight i ^ ((σ : ℂ).re) := by
    refine (hprod.mul_left ((2 * π) ^ (-σ))).congr fun i => ?_
    rw [norm_one, Complex.ofReal_re, one_div_coneWeight_rpow]
  have hM : HasSum (fun i : ℕ × ℕ => Complex.Gamma (σ : ℂ) * 1 / ((coneWeight i : ℝ) : ℂ) ^ (σ : ℂ))
      (mellin (fun t => (coneCount t : ℂ)) (σ : ℂ)) :=
    hasSum_mellin (fun i => Or.inr (coneWeight_pos i))
      (by rw [Complex.ofReal_re]; linarith) hF hsum
  have hval : HasSum (fun i : ℕ × ℕ => Real.Gamma σ * (2 * π) ^ (-σ) *
      (((i.1 : ℝ) + 1) ^ (-σ) * ((i.2 : ℝ) + 1) ^ (-σ))) (coneMellinValue σ) := by
    have e : (∑' m : ℕ, ((m : ℝ) + 1) ^ (-σ)) ^ 2 =
        ∑' i : ℕ × ℕ, ((i.1 : ℝ) + 1) ^ (-σ) * ((i.2 : ℝ) + 1) ^ (-σ) := by
      rw [sq, tsum_mul_tsum_of_summable_norm]
      · exact summable_norm_iff.mpr hps
      · exact summable_norm_iff.mpr hps
    unfold coneMellinValue
    rw [e]
    exact hprod.hasSum.mul_left _
  have hval' : HasSum (fun i : ℕ × ℕ => Complex.Gamma (σ : ℂ) * 1 /
      ((coneWeight i : ℝ) : ℂ) ^ (σ : ℂ)) (coneMellinValue σ : ℂ) :=
    (Complex.hasSum_ofReal.mpr hval).congr_fun fun i => coneTerm_eq σ i
  exact hM.unique hval'

/-! ### The double pole -/

/-- Real `σ → 1⁺` maps into the punctured complex neighbourhood of `1`. -/
theorem tendsto_ofReal_nhdsGT_one : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.tendsto' 1 1 (by simp) |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have h1 : σ = 1 := by exact_mod_cast h
  exact (ne_of_gt (show (1 : ℝ) < σ from hσ)) h1

/-- The real `p`-series has residue `1` at `σ = 1`. -/
theorem tendsto_sub_one_mul_pSeries :
    Tendsto (fun σ : ℝ => (σ - 1) * ∑' m : ℕ, ((m : ℝ) + 1) ^ (-σ)) (𝓝[>] 1) (𝓝 1) := by
  have h := riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one
  have hre := (Complex.continuous_re.tendsto 1).comp h
  simp only [Complex.one_re] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Function.comp_apply]
  rw [riemannZeta_ofReal_eq_tsum (show 1 < σ from hσ), ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Double pole**: `(σ − 1)² Γ(σ)(2π)^{−σ}ζ(σ)² → 1/(2π)` as `σ → 1⁺`. -/
theorem tendsto_sq_mul_coneMellin :
    Tendsto (fun σ : ℝ => (σ - 1) ^ 2 * coneMellinValue σ) (𝓝[>] 1) (𝓝 ((2 * π)⁻¹)) := by
  have hG : Tendsto Real.Gamma (𝓝[>] 1) (𝓝 1) := by
    have := (Real.differentiableAt_Gamma (s := 1) (fun m h => by
      have : (1 : ℝ) = -(m : ℝ) := h
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])).continuousAt.tendsto
    rw [Real.Gamma_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun σ : ℝ => (2 * π) ^ (-σ)) (𝓝[>] 1) (𝓝 ((2 * π)⁻¹)) := by
    have hc : ContinuousAt (fun σ : ℝ => (2 * π) ^ (-σ)) 1 :=
      (Real.continuousAt_const_rpow (by positivity)).comp continuousAt_neg
    have := hc.tendsto
    rw [show (2 * π) ^ (-(1 : ℝ)) = (2 * π)⁻¹ by rw [Real.rpow_neg_one]] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hZ := tendsto_sub_one_mul_pSeries
  have := (hG.mul hP).mul (hZ.pow 2)
  rw [one_mul, one_pow, mul_one] at this
  refine this.congr fun σ => ?_
  rw [coneMellinValue]; ring

/-- **Gaussian Poisson pairs have at most a simple pole at `1`**: for every weak FE-pair,
`(σ − 1)² Λ(σ) → 0` as `σ → 1⁺`. -/
theorem tendsto_sq_mul_Λ (P : WeakFEPair ℂ) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) ^ 2 * P.Λ σ) (𝓝[>] 1) (𝓝 0) := by
  by_cases hk : P.k = 1
  · have hres := P.Λ_residue_k
    rw [hk] at hres
    simp only [Complex.ofReal_one, smul_eq_mul] at hres
    have h1 := hres.comp tendsto_ofReal_nhdsGT_one
    have h2 : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝[>] 1) (𝓝 0) := by
      have hc : Continuous fun σ : ℝ => (σ : ℂ) - 1 := Complex.continuous_ofReal.sub continuous_const
      have := hc.tendsto 1
      simp only [Complex.ofReal_one, sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := h2.mul h1
    rw [zero_mul] at this
    refine this.congr fun σ => ?_
    simp only [Function.comp_apply]; ring
  · have hdiff : DifferentiableAt ℂ P.Λ 1 := P.differentiableAt_Λ (Or.inl one_ne_zero)
      (Or.inl (by
        intro h
        apply hk
        exact_mod_cast h.symm))
    have hc : ContinuousAt (fun s : ℂ => (s - 1) ^ 2 * P.Λ s) 1 :=
      ((continuous_id.sub continuous_const).pow 2).continuousAt.mul hdiff.continuousAt
    have hof : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
      have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    have := hc.tendsto.comp hof
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    exact this

/-- **The isotropic count is not Poisson-dual.** No weak FE-pair has the Mellin transform of the
cone count as its completed function on `σ > 1`. -/
theorem not_exists_FEPair_coneCount :
    ¬ ∃ P : WeakFEPair ℂ, ∀ σ : ℝ, 1 < σ →
      P.Λ σ = mellin (fun t => (coneCount t : ℂ)) (σ : ℂ) := by
  rintro ⟨P, hP⟩
  have h1 := tendsto_sq_mul_Λ P
  have h2 : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) ^ 2 * P.Λ σ) (𝓝[>] 1)
      (𝓝 (((2 * π)⁻¹ : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp tendsto_sq_mul_coneMellin
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Function.comp_apply]
    rw [hP σ hσ, mellin_coneCount hσ]
    push_cast; ring
  have := tendsto_nhds_unique h1 h2
  have hpos : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  exact hpos.ne' (by exact_mod_cast this.symm)

/-! ### Siegel–Weil for the split plane -/

/-- **Siegel–Weil for the split plane.** Averaging the positive-cone Epstein series of the Siegel
majorants over the whole boost line gives the Mellin transform of the indefinite cone count, up to
the archimedean factors: `Γ(σ)(2π)^{−σ} ∫ Z⁺(σ, u) du = K(σ, 0) · Γ(σ)(2π)^{−σ}ζ(σ)²`. Both sides
are `ζ(σ)²` times archimedean constants. -/
theorem siegelWeil_splitPlane {σ : ℝ} (hσ : 1 < σ) :
    Real.Gamma σ * (2 * π) ^ (-σ) * ∫ u, splitSeries σ u * Real.exp (2 * 0 * u) =
      boostConstant σ 0 * coneMellinValue σ := by
  rw [integral_splitSeries_mul_exp (by simp; linarith), coneMellinValue]
  simp only [add_zero, sub_zero]
  ring

end GaloisForLFunctions.LatticeSectionTheory
