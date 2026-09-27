import GaloisForLFunctions.RHTower.LowHeightWeilTests

/-!
# Weil tests with an arbitrary polynomial factor

For a real even `C²` weight `w` supported in `[-1, 1]`, a nonzero polynomial `Q` and
`N ≥ deg Q + 1`, the root convolution over the roots of `Q` followed by `N - deg Q - 1` plain
convolutions with `w` is a `C²` test supported in `[-N, N]` whose transform at `z` is

```text
ŵ(z - γ₀)^N · Q(z - γ₀) / lc(Q)
```

(`polyTest_props`, `polyProfile_eq`).  When `Q` has real coefficients the transform is real
structured, so the Weil summand at a zero `ρ` is `m_ρ F(γ_ρ - γ₀)²` (`Wsummand_polyTest`).  A root
of `Q` at `±i/2 - γ₀` makes the test polar-constrained (`polyTest_polar_zero`).
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- The polynomial test `e^{-iγ₀u}·(w^{⋆k} ⋆ root convolution over the roots of Q)(u)`,
`k = N - deg Q - 1`. -/
def polyTest (γ₀ : ℝ) (w : ℝ → ℝ) (N : ℕ) (Q : ℂ[X]) : ℝ → ℂ :=
  fun u => cexp (-(I * γ₀ * u)) *
    plainConv w (N - (Q.roots.card + 1)) (rootConv w Q.roots.toList) u

/-- The transform profile of the polynomial test: `ŵ(x)^N Π_{roots}(x - r)`. -/
def polyProfile (w : ℝ → ℝ) (N : ℕ) (Q : ℂ[X]) (x : ℂ) : ℂ :=
  paperFT (fun u => (w u : ℂ)) x ^ N * (Q.roots.toList.map (fun r => x - r)).prod

theorem prod_toList_map_sub (Q : ℂ[X]) (x : ℂ) :
    (Q.roots.toList.map (fun r => x - r)).prod = (Q.roots.map (fun r => x - r)).prod := by
  conv_rhs => rw [← Multiset.coe_toList Q.roots]
  rw [Multiset.map_coe, Multiset.prod_coe]

/-- The profile in terms of `Q`: `ŵ(x)^N Q(x)/lc(Q)`. -/
theorem polyProfile_eq (w : ℝ → ℝ) (N : ℕ) {Q : ℂ[X]} (hQ : Q ≠ 0) (x : ℂ) :
    polyProfile w N Q x =
      paperFT (fun u => (w u : ℂ)) x ^ N * (Q.eval x / Q.leadingCoeff) := by
  unfold polyProfile
  congr 1
  rw [prod_toList_map_sub]
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q)
    IsAlgClosed.card_roots_eq_natDegree
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have he : Q.eval x = Q.leadingCoeff * (Q.roots.map (fun r => x - r)).prod := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl fun r _ => by simp
  rw [he]
  field_simp

theorem polyTest_props {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (γ₀ : ℝ) {N : ℕ} {Q : ℂ[X]}
    (hN : Q.natDegree + 1 ≤ N) :
    ContDiff ℝ 2 (polyTest γ₀ w N Q) ∧
      (∀ u, polyTest γ₀ w N Q u ≠ 0 → |u| ≤ N) ∧
      ∀ z, paperFT (polyTest γ₀ w N Q) z = polyProfile w N Q (z - γ₀) := by
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hlen : Q.roots.toList.length = Q.roots.card := Multiset.length_toList _
  obtain ⟨hrc, hrs, hrf⟩ := rootConv_props hw heven hsupp Q.roots.toList
  obtain ⟨hpc, hps, hpf⟩ := plainConv_props hw heven hsupp hrc hrs (N - (Q.roots.card + 1))
  have hk : N - (Q.roots.card + 1) + (Q.roots.card + 1) = N := by omega
  refine ⟨?_, fun u hu => ?_, fun z => ?_⟩
  · unfold polyTest
    have h1 : ContDiff ℝ 2 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ 2 (fun u : ℝ => -(I * (γ₀ : ℂ) * (u : ℂ))) := (contDiff_const.mul h1).neg
    exact (Complex.contDiff_exp.comp h2).mul hpc
  · have hne : plainConv w (N - (Q.roots.card + 1)) (rootConv w Q.roots.toList) u ≠ 0 := by
      intro h; apply hu; simp [polyTest, h]
    have := hps u hne
    rw [hlen] at this
    have e : ((Q.roots.card : ℝ) + 1) * 1 + ((N - (Q.roots.card + 1) : ℕ) : ℝ) * 1 = N := by
      rw [mul_one, mul_one]
      have := congrArg (fun k : ℕ => (k : ℝ)) hk
      push_cast at this ⊢
      linarith
    linarith
  · unfold polyTest
    rw [paperFT_modulate, hpf, hrf, hlen, polyProfile]
    have hp : paperFT (fun u => (w u : ℂ)) (z - γ₀) ^ N =
        paperFT (fun u => (w u : ℂ)) (z - γ₀) ^ (Q.roots.card + 1) *
          paperFT (fun u => (w u : ℂ)) (z - γ₀) ^ (N - (Q.roots.card + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]
    ring

/-- `conj (Q(conj x)) = Q(x)` for a polynomial with real coefficients. -/
theorem conj_eval_conj_of_real {Q : ℂ[X]} (hQ : ∀ n, conj (Q.coeff n) = Q.coeff n) (x : ℂ) :
    conj (Q.eval (conj x)) = Q.eval x := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_pow, Complex.conj_conj, hQ]

/-- Real structure: the Weil summand of the polynomial test is `m F(x_ρ)²`. -/
theorem Wsummand_polyTest {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (Z : ZeroConfig) (γ₀ : ℝ) {N : ℕ} {Q : ℂ[X]}
    (hQ0 : Q ≠ 0) (hQ : ∀ n, conj (Q.coeff n) = Q.coeff n) (hN : Q.natDegree + 1 ≤ N)
    (ρ : ℂ) :
    Z.Wsummand (polyTest γ₀ w N Q) (polyTest γ₀ w N Q) ρ =
      (Z.mult ρ : ℂ) * polyProfile w N Q (gammaOf ρ - γ₀) ^ 2 := by
  obtain ⟨-, -, hf⟩ := polyTest_props hw heven hsupp γ₀ hN
  rw [ZeroConfig.Wsummand, hf, hf]
  have hc : conj (gammaOf ρ) - (γ₀ : ℂ) = conj (gammaOf ρ - γ₀) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [hc]
  have hlc : conj Q.leadingCoeff = Q.leadingCoeff := hQ _
  have hreal : ∀ y : ℂ, conj (polyProfile w N Q (conj y)) = polyProfile w N Q y := by
    intro y
    rw [polyProfile_eq w N hQ0, polyProfile_eq w N hQ0, map_mul, map_pow,
      conj_paperFT_conj_of_even heven, map_div₀, conj_eval_conj_of_real hQ, hlc]
  rw [hreal]
  ring

/-- A root of `Q` at `±i/2 - γ₀` makes the polynomial test vanish at the poles. -/
theorem polyTest_polar_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (γ₀ : ℝ) {N : ℕ} {Q : ℂ[X]} (hQ0 : Q ≠ 0)
    (hN : Q.natDegree + 1 ≤ N) {z : ℂ} (hz : Q.eval (z - γ₀) = 0) :
    paperFT (polyTest γ₀ w N Q) z = 0 := by
  obtain ⟨-, -, hf⟩ := polyTest_props hw heven hsupp γ₀ hN
  rw [hf, polyProfile_eq w N hQ0, hz, zero_div, mul_zero]

end RHTower
