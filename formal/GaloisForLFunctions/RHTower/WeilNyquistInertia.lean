import GaloisForLFunctions.RHTower.WeilFloorSpectralSeparation
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The Nyquist inertia law for the finite-level Weil form

The `ε`-negative index `weilNegIndex ζ a ε` of the level-`a` Weil form is the largest dimension
of a space of polar-constrained `C²` tests on `[-a, a]` on which `Re W(f, f) < -ε ∫|f|²`.
It is bounded above by the number of off-line pairs below `exp(O(e^a) + O(log 1/ε))`
(`zeta_weil_inertia_law`).

**Nyquist inertia law** (`weilNegIndex_ge_card_offline_zeros`). Let `T` be a finite set of zeros
`β + it` with `β > ½`, `t ≥ 101`, ordinates pairwise at least `3/2` apart, and all below the
Nyquist condition of `HodgeClusterNyquistExclusion` with a `log |T|` margin. Then
`weilNegIndex ζ a (1/(K₁ a |T| Λ²)) ≥ |T|`, where `Λ ≈ e^{πt/4 + polylog}` is the size of the
cluster tests.

No isolation of the zeros, no depth-dependent visibility height and no loss from the polar
constraints enters. Below the Nyquist height `≈ 2e^{2a}`, every off-line zero is a negative
square of the finite-level Weil form, whatever the configuration of its neighbours.

The proof has three parts.

* The cluster test of each zero has transform `±i` at its own nodes and at most the tail `η`
  at every other zero. Two setups at heights `3/2` apart have disjoint, reflection-closed node
  sets. So each summand of the cross term `W(f, f')` has one small factor, and
  `‖W(f, f')‖ ≤ (5/4) S_Z (η E' + η' E)` (`norm_W_le_of_split`, `norm_W_cluster_tests_le`).
* The diagonal entries are at most `-3/8 + O(η)` (`ClusterSetup.re_W_test_le`).
* A diagonally dominant Weil Gram matrix gives a negative subspace of full dimension
  (`exists_negative_subspace_of_gram`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- **Split cross term.** Let `f, g` be `C²` tests supported in `[-a, a]`. Suppose `f̂(γ_ρ)` is at
most `η_f` at every zero outside a set `F`, and `ĝ(conj γ_ρ)` is at most `η_g` at every zero of
`F`. Then `‖W(f, g)‖ ≤ (5/4) S_Z (η_f E_g + η_g E_f)`, with `E = e^{a/2} · 4(‖·‖₁ + ‖·''‖₁)`. -/
theorem norm_W_le_of_split {f g : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a) (hgs : ∀ u, g u ≠ 0 → |u| ≤ a)
    (F : Set zetaZeroConfig.carrier) {ηf ηg : ℝ} (hηf : 0 ≤ ηf) (hηg : 0 ≤ ηg)
    (hfo : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F → ‖paperFT f (gammaOf (ρ : ℂ))‖ ≤ ηf)
    (hgo : ∀ ρ : zetaZeroConfig.carrier, ρ ∈ F →
      ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤ ηg) :
    ‖zetaZeroConfig.W f g‖ ≤ (5 / 4) * zeroSumZ *
      (ηf * (Real.exp (a / 2) * (4 * ((∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖))) +
        ηg * (Real.exp (a / 2) * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)))) := by
  have hdec : ∀ c : ℝ → ℂ, ContDiff ℝ 2 c → (∀ u, c u ≠ 0 → |u| ≤ a) →
      ∀ ρ : zetaZeroConfig.carrier, ∀ z : ℂ, |z.im| ≤ 1 / 2 → |z.re| = |(ρ : ℂ).im| →
        ‖paperFT c z‖ ≤ Real.exp (a / 2) * (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)) *
          ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) := by
    intro c hc hcs ρ z hz hre
    have h := norm_paperFT_le_decay hc hcs z
    rw [hre] at h
    have hN1 : 0 ≤ ∫ u, ‖c u‖ := integral_nonneg fun u => norm_nonneg _
    have hN2 : 0 ≤ ∫ u, ‖deriv (deriv c) u‖ := integral_nonneg fun u => norm_nonneg _
    obtain ⟨N, hNdef⟩ : ∃ x, x = 4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖) := ⟨_, rfl⟩
    rw [← hNdef] at h ⊢
    have hN : 0 ≤ N := by rw [hNdef]; positivity
    have hea : Real.exp (|z.im| * a) ≤ Real.exp (a / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
    have hq := one_div_one_add_abs_im_sq_le (zetaZeroConfig.strip ρ ρ.2)
    have hp : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
    calc ‖paperFT c z‖ ≤ Real.exp (|z.im| * a) * N / (1 + |(ρ : ℂ).im|) ^ 2 := h
      _ = Real.exp (|z.im| * a) * N * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring
      _ ≤ Real.exp (a / 2) * N * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hea hN) hq (by positivity)
            (mul_nonneg (Real.exp_pos _).le hN)
  have hpt : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 ∧
      |(gammaOf (ρ : ℂ)).re| = |(ρ : ℂ).im| ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re| = |(ρ : ℂ).im| := by
    intro ρ
    have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := ρ.2
      exact ⟨h.2.1, h.2.2⟩
    have hIm := (WeilEF.abs_gammaOf_im_lt hstrip).le
    refine ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, by rw [WeilEF.gammaOf_re],
      by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩
  obtain ⟨Ef, hEf⟩ : ∃ x, x = Real.exp (a / 2) * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) :=
    ⟨_, rfl⟩
  obtain ⟨Eg, hEg⟩ : ∃ x, x = Real.exp (a / 2) * (4 * ((∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖)) :=
    ⟨_, rfl⟩
  rw [← hEf, ← hEg]
  have hEf0 : 0 ≤ Ef := by
    have h1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun u => norm_nonneg _
    rw [hEf]; positivity
  have hEg0 : 0 ≤ Eg := by
    have h1 : 0 ≤ ∫ u, ‖g u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv g) u‖ := integral_nonneg fun u => norm_nonneg _
    rw [hEg]; positivity
  set Cc : ℝ := (5 / 4) * (ηf * Eg + ηg * Ef) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hb : ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      Cc * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4⟩ := hpt ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    obtain ⟨q, hqdef⟩ : ∃ x, x = 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by
      rw [hqdef]; exact one_div_nonneg.mpr (add_nonneg zero_le_one (Complex.normSq_nonneg _))
    have e : (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) =
        (zetaZeroConfig.mult ρ : ℝ) * q := by rw [hqdef]; ring
    rw [e]
    have hn : ‖zetaZeroConfig.Wsummand f g ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ := by
      simp only [ZeroConfig.Wsummand]
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    rw [hn]
    have dF := hdec f hf hfs ρ _ h1 h3
    have dG := hdec g hg hgs ρ _ h2 h4
    rw [← hEf, ← hqdef] at dF
    rw [← hEg, ← hqdef] at dG
    have hA := norm_nonneg (paperFT f (gammaOf (ρ : ℂ)))
    have hB := norm_nonneg (paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ))))
    by_cases hρ : ρ ∈ F
    · have hB' := hgo ρ hρ
      calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf (ρ : ℂ))‖ *
            ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          ≤ (zetaZeroConfig.mult ρ : ℝ) * (Ef * ((5 / 4) * q)) * ηg :=
            mul_le_mul (mul_le_mul_of_nonneg_left dF hm) hB' hB (by positivity)
        _ = (5 / 4) * (ηg * Ef) * ((zetaZeroConfig.mult ρ : ℝ) * q) := by ring
        _ ≤ Cc * ((zetaZeroConfig.mult ρ : ℝ) * q) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hm hq0)
            rw [hCc]; nlinarith [mul_nonneg hηf hEg0]
    · have hA' := hfo ρ hρ
      calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf (ρ : ℂ))‖ *
            ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          ≤ (zetaZeroConfig.mult ρ : ℝ) * ηf * (Eg * ((5 / 4) * q)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hA' hm) dG hB (by positivity)
        _ = (5 / 4) * (ηf * Eg) * ((zetaZeroConfig.mult ρ : ℝ) * q) := by ring
        _ ≤ Cc * ((zetaZeroConfig.mult ρ : ℝ) * q) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hm hq0)
            rw [hCc]; nlinarith [mul_nonneg hηg hEf0]
  have hsB : Summable (fun ρ : zetaZeroConfig.carrier =>
      Cc * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    summable_zeroSumZ.mul_left _
  have hs : Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f g ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsB
  calc ‖zetaZeroConfig.W f g‖ = ‖∑' ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand f g ρ‖ := by
        rw [ZeroConfig.W]
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ : zetaZeroConfig.carrier,
          Cc * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        Summable.tsum_le_tsum hb hs hsB
    _ = Cc * zeroSumZ := by rw [tsum_mul_left]; rfl
    _ = (5 / 4) * zeroSumZ * (ηf * Eg + ηg * Ef) := by rw [hCc]; ring

/-- **Gram negativity.** Let `f_i` (`i ∈ ι`, finite) be polar-constrained `C²` tests on `[-a, a]`
whose Weil Gram matrix is diagonally dominant: `Re W(f_i, f_i) ≤ -3/8 + D`, `‖W(f_i, f_j)‖ ≤ O`
for `i ≠ j`, and `D + (|ι| - 1) O ≤ 1/8`. If `∫|f_i|² ≤ M` and `ε |ι| M ≤ 1/8`, then the span of
the `f_i` has dimension `|ι|` and `Re W(g, g) < -ε ∫|g|²` on it off `0`. -/
theorem exists_negative_subspace_of_gram {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    {a D O M ε : ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i)) (hs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    (hp1 : ∀ i, paperFT (f i) (I / 2) = 0) (hp2 : ∀ i, paperFT (f i) (-(I / 2)) = 0)
    (hdiag : ∀ i, (zetaZeroConfig.W (f i) (f i)).re ≤ -(3 / 8) + D)
    (hoff : ∀ i j, i ≠ j → ‖zetaZeroConfig.W (f i) (f j)‖ ≤ O) (hO : 0 ≤ O)
    (hDO : D + ((Fintype.card ι : ℝ) - 1) * O ≤ 1 / 8)
    (hM : ∀ i, ∫ u, ‖f i u‖ ^ 2 ≤ M) (hε : 0 ≤ ε)
    (hεM : ε * (Fintype.card ι * M) ≤ 1 / 8) :
    ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧ Module.finrank ℂ V = Fintype.card ι ∧
      (∀ g ∈ V, ContDiff ℝ 2 g ∧ tsupport g ⊆ Icc (-a) a ∧ paperFT g (I / 2) = 0 ∧
        paperFT g (-(I / 2)) = 0) ∧
      ∀ g ∈ V, g ≠ 0 → (zetaZeroConfig.W g g).re < -(ε * ∫ u, ‖g u‖ ^ 2) := by
  classical
  have hcomp : ∀ i, HasCompactSupport (f i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hs i)
  have hcont : ∀ i, Continuous (f i) := fun i => (hf i).continuous
  let Γ : (ι → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := fun c u => ∑ i, c i * f i u
      map_add' := fun c d => by
        funext u; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun k c => by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΓ : ∀ c, Γ c = fun u => ∑ i, c i * f i u := fun c => rfl
  have hsum : ∀ i j, Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand (f i) (f j) ρ) := fun i j =>
    zeta_Wsummand_summable (hf i) (hf j) (hcomp i) (hcomp j)
  have hWΓ : ∀ c : ι → ℂ, zetaZeroConfig.W (Γ c) (Γ c) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * zetaZeroConfig.W (f i) (f j) := fun c =>
    W_finset_sum zetaZeroConfig Finset.univ c hcont hcomp hsum
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  -- the Gram bound
  have hkey : ∀ c : ι → ℂ, (zetaZeroConfig.W (Γ c) (Γ c)).re ≤ -(1 / 4) * ∑ i, ‖c i‖ ^ 2 := by
    intro c
    rw [hWΓ, Complex.re_sum]
    simp only [Complex.re_sum]
    set S := ∑ i, ‖c i‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, (c i * (starRingEnd ℂ) (c j) * zetaZeroConfig.W (f i) (f j)).re ≤
        (if i = j then ‖c i‖ ^ 2 * (-(3 / 8) + D - O) else 0) +
          (O / 2 * ‖c i‖ ^ 2 + O / 2 * ‖c j‖ ^ 2) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have e : c i * (starRingEnd ℂ) (c i) = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [e, Complex.re_ofReal_mul]
        have := hdiag i
        have h2 : 0 ≤ ‖c i‖ ^ 2 := sq_nonneg _
        nlinarith
      · rw [if_neg hij, zero_add]
        have h1 := Complex.re_le_norm (c i * (starRingEnd ℂ) (c j) * zetaZeroConfig.W (f i) (f j))
        rw [norm_mul, norm_mul, RCLike.norm_conj] at h1
        have h2 := hoff i j hij
        have h3 : ‖c i‖ * ‖c j‖ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
        have h4 : ‖c i‖ * ‖c j‖ * ‖zetaZeroConfig.W (f i) (f j)‖ ≤ ‖c i‖ * ‖c j‖ * O :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h5 : ‖c i‖ * ‖c j‖ * O ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 * O :=
          mul_le_mul_of_nonneg_right h3 hO
        linarith
    have hA : ∑ i, ∑ j, (if i = j then ‖c i‖ ^ 2 * (-(3 / 8) + D - O) else 0) =
        S * (-(3 / 8) + D - O) := by
      simp [Finset.sum_ite_eq, hS, Finset.sum_mul]
    have hB : ∑ i : ι, ∑ j : ι, (O / 2 * ‖c i‖ ^ 2 + O / 2 * ‖c j‖ ^ 2) = O * n * S := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      rw [hn, hS]; ring
    calc ∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j) * zetaZeroConfig.W (f i) (f j)).re
        ≤ ∑ i, ∑ j, ((if i = j then ‖c i‖ ^ 2 * (-(3 / 8) + D - O) else 0) +
          (O / 2 * ‖c i‖ ^ 2 + O / 2 * ‖c j‖ ^ 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = S * (-(3 / 8) + D - O) + O * n * S := by
          rw [← hA, ← hB, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
      _ = S * (-(3 / 8) + (D + (n - 1) * O)) := by ring
      _ ≤ S * (-(3 / 8) + 1 / 8) := by
          apply mul_le_mul_of_nonneg_left _ hS0; linarith
      _ = -(1 / 4) * S := by ring
  -- supports
  have hsuppΓ : ∀ c u, Γ c u ≠ 0 → u ∈ Icc (-a) a := by
    intro c u h
    rw [hΓ] at h
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact hs i (subset_tsupport _ (right_ne_zero_of_mul hi))
  have hΓs : ∀ c, HasCompactSupport (Γ c) := fun c =>
    HasCompactSupport.intro isCompact_Icc fun u hu => by
      by_contra h; exact hu (hsuppΓ c u h)
  have hΓc : ∀ c, Continuous (Γ c) := fun c => by
    rw [hΓ]; exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcont i)
  -- the `L²` bound
  have hL2 : ∀ c : ι → ℂ, ∫ u, ‖Γ c u‖ ^ 2 ≤ n * (∑ i, ‖c i‖ ^ 2) * M := by
    intro c
    have iF : ∀ i, Integrable (fun u => ‖c i‖ ^ 2 * ‖f i u‖ ^ 2) := by
      intro i
      have hc2 : HasCompactSupport (fun u => ‖f i u‖ ^ 2) := by
        have : (fun u => ‖f i u‖ ^ 2) = fun u => ‖f i u‖ * ‖f i u‖ := funext fun u => sq _
        rw [this]; exact (hcomp i).norm.mul_right
      exact (((hcont i).norm.pow 2).integrable_of_hasCompactSupport hc2).const_mul _
    have iG : Integrable (fun u => ‖Γ c u‖ ^ 2) := by
      have hc2 : HasCompactSupport (fun u => ‖Γ c u‖ ^ 2) := by
        have : (fun u => ‖Γ c u‖ ^ 2) = fun u => ‖Γ c u‖ * ‖Γ c u‖ := funext fun u => sq _
        rw [this]; exact (hΓs c).norm.mul_right
      exact ((hΓc c).norm.pow 2).integrable_of_hasCompactSupport hc2
    have iS : Integrable (fun u => n * ∑ i, ‖c i‖ ^ 2 * ‖f i u‖ ^ 2) :=
      (integrable_finsetSum _ fun i _ => iF i).const_mul _
    have hpt : ∀ u, ‖Γ c u‖ ^ 2 ≤ n * ∑ i, ‖c i‖ ^ 2 * ‖f i u‖ ^ 2 := by
      intro u
      have h1 : ‖Γ c u‖ ≤ ∑ i, ‖c i‖ * ‖f i u‖ := by
        rw [hΓ]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
      have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖c i‖ * ‖f i u‖)
      rw [Finset.card_univ] at h2
      have h3 : ‖Γ c u‖ ^ 2 ≤ (∑ i, ‖c i‖ * ‖f i u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ‖Γ c u‖ ^ 2 ≤ (∑ i, ‖c i‖ * ‖f i u‖) ^ 2 := h3
        _ ≤ (Fintype.card ι : ℝ) * ∑ i, (‖c i‖ * ‖f i u‖) ^ 2 := by exact_mod_cast h2
        _ = n * ∑ i, ‖c i‖ ^ 2 * ‖f i u‖ ^ 2 := by
            rw [hn]; congr 1; exact Finset.sum_congr rfl fun i _ => mul_pow _ _ _
    calc ∫ u, ‖Γ c u‖ ^ 2 ≤ ∫ u, n * ∑ i, ‖c i‖ ^ 2 * ‖f i u‖ ^ 2 :=
          integral_mono iG iS hpt
      _ = n * ∑ i, ‖c i‖ ^ 2 * ∫ u, ‖f i u‖ ^ 2 := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => iF i]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ n * ∑ i, ‖c i‖ ^ 2 * M := by
          apply mul_le_mul_of_nonneg_left _ (by rw [hn]; positivity)
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (sq_nonneg _)
      _ = n * (∑ i, ‖c i‖ ^ 2) * M := by rw [← Finset.sum_mul]; ring
  -- injectivity
  have hW0 : zetaZeroConfig.W 0 0 = 0 := by
    rw [ZeroConfig.W]
    have : ∀ ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand 0 0 ρ = 0 := fun ρ => by
      simp [ZeroConfig.Wsummand, paperFT_def]
    simp [this]
  have hSpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < ∑ i, ‖c i‖ ^ 2 := by
    intro c hc
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    have h1 : 0 < ‖c i‖ ^ 2 := by
      have : 0 < ‖c i‖ := norm_pos_iff.mpr hi
      positivity
    have := Finset.single_le_sum (f := fun i => ‖c i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
    linarith
  have hinj : Function.Injective Γ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    by_contra hc0
    have h1 := hkey c
    have h2 := hSpos c hc0
    rw [hc, hW0, Complex.zero_re] at h1
    linarith
  refine ⟨LinearMap.range Γ, inferInstance, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  · intro g hg
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hg
    refine ⟨?_, closure_minimal (fun u hu => hsuppΓ c u hu) isClosed_Icc, ?_, ?_⟩
    · rw [hΓ]; exact ContDiff.sum fun i _ => contDiff_const.mul (hf i)
    · rw [hΓ, paperFT_finset_sum Finset.univ c hcont hcomp]; simp [hp1]
    · rw [hΓ, paperFT_finset_sum Finset.univ c hcont hcomp]; simp [hp2]
  · intro g hg hg0
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hg
    have hc0 : c ≠ 0 := by intro h; apply hg0; rw [h, map_zero]
    have h1 := hkey c
    have h2 := hL2 c
    have h3 := hSpos c hc0
    set S := ∑ i, ‖c i‖ ^ 2
    have h4 : ε * ∫ u, ‖Γ c u‖ ^ 2 ≤ ε * (n * S * M) := mul_le_mul_of_nonneg_left h2 hε
    have h5 : ε * (n * S * M) = S * (ε * (n * M)) := by ring
    have h6 : S * (ε * (n * M)) ≤ S * (1 / 8) := mul_le_mul_of_nonneg_left hεM h3.le
    linarith


local notation "Φ" => riemannPhiKernel
local notation "shw" => OffLinePairData.sh
local notation "Mθ" => jacobiThetaTailConstant

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The truncation tail `η = 6 Σ|c_k| · tail(K)` of the cluster test at level `a`. -/
def testTail (a : ℝ) : ℝ := 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - shw)

theorem testTail_nonneg (a : ℝ) : 0 ≤ C.testTail a := by
  unfold testTail
  have := coeffMass_nonneg C.Q; have := expTail_nonneg C.K (1 / 2) (a - 1 / 4 - shw)
  positivity

/-- The bound `4 Kp Σ|c_k| (1 + cosh(s/2)) (t₀+3)² B` for `‖f‖₁ + ‖f''‖₁` of the cluster test. -/
def normBound (Kp : ℝ) : ℝ :=
  4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
    ((1 + (C.t₀ + 2)) ^ 2 * C.Bk)

/-- The cluster test is a polar-constrained `C²` test on `[-a, a]` with
`‖f‖₁ + ‖f''‖₁ ≤ normBound`. -/
theorem test_properties {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ}
    (hKp2 : 2 ≤ Kp) (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    ContDiff ℝ 2 (C.test a) ∧ (∀ u, C.test a u ≠ 0 → |u| ≤ a) ∧
      tsupport (C.test a) ⊆ Icc (-a) a ∧ paperFT (C.test a) (I / 2) = 0 ∧
      paperFT (C.test a) (-(I / 2)) = 0 ∧
      (∫ u, ‖C.test a u‖) + (∫ u, ‖deriv (deriv (C.test a)) u‖) ≤ C.normBound Kp := by
  obtain ⟨hK, -, -⟩ := C.K_spec
  obtain ⟨k₁, k₂, hd1, hd2, ck₁, ck₂, ik₁, ik₂, nh, nk₁, nk₂⟩ := C.K_calculus hρ₀
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  obtain ⟨hC2, hN12⟩ := clusterTest_calculus hK hd1 hd2 ck₁ ck₂ ik₁ ik₂ hΓ nh nk₁ nk₂ C.Q C.κ
    (heightPolarShift C.t₀) (a - 1 / 4) hKp2 hKp
  have hsp0 : 0 ≤ heightPolarShift C.t₀ := by linarith [(heightPolarShift_mem C.ht₀).1]
  refine ⟨hC2, clusterTest_supp C.κ_pos.le hsp0 (C.test_supp_bound a),
    tsupport_clusterTest C.κ_pos.le hsp0 (C.test_supp_bound a), ?_, ?_, hN12⟩
  · unfold test; rw [paperFT_clusterTest hK, polarSymbol_half_I]; ring
  · unfold test; rw [paperFT_clusterTest hK, polarSymbol_neg_half_I]; ring

/-- The transform of the test at a divisor point that is not a node is at most the tail. -/
theorem test_off_support (a : ℝ) {ν : XiDivisorSupport} (hν : ν ∉ C.nodes) :
    ‖paperFT (C.test a) (gammaOf (ν : ℂ))‖ ≤ C.testTail a :=
  C.test_off_node a (ρ := toCarrier ν) fun μ hμ e => hν (by
    have : ν = μ := Subtype.ext e
    rw [this]; exact hμ)

/-- Nodes lie within `3/4` of the height. -/
theorem node_im_near {ν : XiDivisorSupport} (hν : ν ∈ C.nodes) : |(ν : ℂ).im - C.t₀| < 3 / 4 := by
  have h := ((mem_nodeSet (by linarith [C.hX2])).mp hν).1
  linarith [C.hX2]

/-- **The diagonal entry.** If `η ≤ 1/4`, then `Re W(f, f) ≤ -3/8 + 5 S_Z η e^{a/2} B'`. -/
theorem re_W_test_le {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) {a : ℝ} (ha : 0 ≤ a) {Kp : ℝ}
    (hKp2 : 2 ≤ Kp) (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp)
    (hη : C.testTail a ≤ 1 / 4) :
    (zetaZeroConfig.W (C.test a) (C.test a)).re ≤
      -(3 / 8) + 5 * zeroSumZ * C.testTail a * Real.exp (a / 2) * C.normBound Kp := by
  classical
  obtain ⟨hC2, hsupp, -, -, -, hN12⟩ := C.test_properties hρ₀ a hKp2 hKp
  have hη0 := C.testTail_nonneg a
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  have hother : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      ‖paperFT (C.test a) (gammaOf (ρ : ℂ))‖ ≤ C.testTail a := by
    intro ρ hρ
    refine C.test_off_node a fun ν hν e => hρ ?_
    rw [hF, Finset.mem_image]
    exact ⟨ν, hν, Subtype.ext e.symm⟩
  have hsplit := re_W_le_nodes_add ha hC2 hsupp F hη0 hother
  have hsumF : ∑ ρ ∈ F, (zetaZeroConfig.Wsummand (C.test a) (C.test a) ρ).re =
      ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re :=
    Finset.sum_image fun x _ y _ h => toCarrier_injective h
  have hsq : C.testTail a ^ 2 ≤ (1 / 4) * C.testTail a := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hη hη0
  have hneg : -1 + 2 * C.testTail a + C.testTail a ^ 2 ≤ -(3 / 8) := by linarith
  have hterm : ∀ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
      (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8)) := by
    intro ν hν
    refine (C.re_summand_node_le a hν).trans ?_
    exact mul_le_mul_of_nonneg_left hneg (Nat.cast_nonneg _)
  have hblock : ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
      -(3 / 8) := by
    rw [← Finset.add_sum_erase _ _ hρ₀]
    have h1 := hterm ρ₀ hρ₀
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ρ₀) := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ (toCarrier ρ₀).2
    have h2 : ∑ ν ∈ C.nodes.erase ρ₀,
        (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤ 0 := by
      refine Finset.sum_nonpos fun ν hν => (hterm ν (Finset.mem_of_mem_erase hν)).trans ?_
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by norm_num)
    linarith
  rw [hsumF] at hsplit
  have hS := zeroSumZ_nonneg
  have hE := Real.exp_pos (a / 2)
  have hR : (5 / 4) * zeroSumZ * (C.testTail a * (Real.exp (a / 2) *
      (4 * ((∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖)))) ≤
      5 * zeroSumZ * C.testTail a * Real.exp (a / 2) * C.normBound Kp := by
    have h1 : (5 / 4) * zeroSumZ * (C.testTail a * (Real.exp (a / 2) *
        (4 * ((∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖)))) =
        5 * zeroSumZ * C.testTail a * Real.exp (a / 2) *
          ((∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hN12 (by positivity)
  linarith

end ClusterSetup

/-- **The cross entry.** Two cluster setups at heights at least `3/2` apart have disjoint,
reflection-closed node sets, and `‖W(f, f')‖ ≤ (5/4) S_Z (η E' + η' E)`. -/
theorem norm_W_cluster_tests_le (C C' : ClusterSetup) (hsep : 3 / 2 ≤ |C.t₀ - C'.t₀|) {a : ℝ}
    (ha : 0 ≤ a) (hf : ContDiff ℝ 2 (C.test a)) (hf' : ContDiff ℝ 2 (C'.test a))
    (hfs : ∀ u, C.test a u ≠ 0 → |u| ≤ a) (hfs' : ∀ u, C'.test a u ≠ 0 → |u| ≤ a) :
    ‖zetaZeroConfig.W (C.test a) (C'.test a)‖ ≤ (5 / 4) * zeroSumZ *
      (C.testTail a * (Real.exp (a / 2) *
          (4 * ((∫ u, ‖C'.test a u‖) + ∫ u, ‖deriv (deriv (C'.test a)) u‖))) +
        C'.testTail a * (Real.exp (a / 2) *
          (4 * ((∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖)))) := by
  have hdisj : ∀ ν, ν ∈ C.nodes → ν ∉ C'.nodes := by
    intro ν h h'
    have h1 := C.node_im_near h
    have h2 := C'.node_im_near h'
    have : |C.t₀ - C'.t₀| < 3 / 2 := by
      rw [abs_lt] at h1 h2 ⊢; constructor <;> linarith
    linarith
  refine norm_W_le_of_split ha hf hf' hfs hfs' (ClusterSetup.toCarrier '' (C.nodes : Set _))
    (C.testTail_nonneg a) (C'.testTail_nonneg a) ?_ ?_
  · intro ρ hρ
    refine C.test_off_node a fun ν hν e => hρ ⟨ν, hν, Subtype.ext e.symm⟩
  · rintro ρ ⟨ν, hν, rfl⟩
    have e : (starRingEnd ℂ) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ)) =
        gammaOf (reflectSupport ν : ℂ) := by
      rw [gammaOf_reflectSupport]; rfl
    rw [e]
    exact C'.test_off_support a (hdisj _ (C.reflect_mem_nodes hν))


/-! ## Explicit sizes -/

/-- The size `2^N B (N+1) M (t+3)²` of the cluster test at the zero `ρ`, with
`N` the window count, `B = max(2^N ∫|Φ|e^{3N|u|/2}, 1)` and `M` the interpolation bound. -/
def nyquistSize (ρ : ℂ) : ℝ :=
  2 ^ windowCount ρ.im * max (2 ^ windowCount ρ.im * expTail Φ (3 / 2 * windowCount ρ.im) 0) 1 *
    ((windowCount ρ.im + 1) * ClusterSetup.interpBound ρ.im (ρ.re - 1 / 2) (windowCount ρ.im)) *
    (ρ.im + 3) ^ 2

/-- The tail `e^{(5 + 3N)X - πe^{2X}}`, `X = a - 3/8`, of Riemann's kernel at level `a`. -/
def nyquistTail (a : ℝ) (ρ : ℂ) : ℝ :=
  Real.exp ((1 / 2 + 3 * (windowCount ρ.im : ℝ) + 9 / 2) * (a - 3 / 8) -
    π * Real.exp (2 * (a - 3 / 8)))

/-- Every off-line zero above height `101` is a node of a cluster setup at its own height. -/
theorem exists_clusterSetup_node {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (ht : 101 ≤ ρ₀.im) :
    ∃ C : ClusterSetup, C.t₀ = ρ₀.im ∧ C.δ₀ = ρ₀.re - 1 / 2 ∧ ∃ ν ∈ C.nodes, (ν : ℂ) = ρ₀ := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero (by
    rw [xi_eq_xiUnit_mul_zeta (fun h => by rw [h] at hβ; norm_num at hβ)
      (fun h => by rw [h] at hnt; exact absurd hnt.2.2 (by norm_num)) hnt.2.1, hnt.1, mul_zero])
  set ν₀ : XiDivisorSupport := q.1
  have hν₀ : (ν₀ : ℂ) = ρ₀ := hq
  obtain ⟨C, hCt, hCδ⟩ := exists_clusterSetup ht (δ₀ := ρ₀.re - 1 / 2) (by linarith)
    (by linarith [hnt.2.2])
  have hν₀N : ν₀ ∈ C.nodes := by
    rw [mem_nodeSet (by linarith [C.hX2]), hν₀, hCt, sub_self, abs_zero]
    refine ⟨by linarith [C.hX1], ?_⟩
    rw [abs_of_pos (by linarith)]
    have := C.hy₁; rw [hCδ] at this; linarith
  exact ⟨C, hCt, hCδ, ν₀, hν₀N, hν₀⟩

namespace ClusterSetup

variable (C : ClusterSetup)

theorem normBound_nonneg {Kp : ℝ} (hKp : 0 ≤ Kp) : 0 ≤ C.normBound Kp := by
  unfold normBound
  have := coeffMass_nonneg C.Q
  have := Real.cosh_pos (heightPolarShift C.t₀ / 2)
  have := C.Bk_nonneg
  have : 0 ≤ 1 + Real.cosh (heightPolarShift C.t₀ / 2) := by linarith
  positivity

/-- The tail of the cluster test below the Nyquist condition. -/
theorem testTail_le (hne : C.nodes.Nonempty) {a : ℝ} (ha : 1 ≤ a)
    (hlam : 1 / 2 + 3 * (windowCount C.t₀ : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8))) :
    C.testTail a ≤ 6 * (80 * Mθ * Real.exp π + 1) *
      (((windowCount C.t₀ + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀)) *
        2 ^ windowCount C.t₀) *
      Real.exp ((1 / 2 + 3 * (windowCount C.t₀ : ℝ) + 9 / 2) * (a - 3 / 8) -
        π * Real.exp (2 * (a - 3 / 8))) := by
  set W := windowCount C.t₀ with hWdef
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  rw [← hMidef]
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  obtain ⟨εΦ, hεΦdef⟩ : ∃ x, x = (80 * Mθ * Real.exp π + 1) *
    Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) :=
    ⟨_, rfl⟩
  have hε : expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) ≤ 2 ^ W * εΦ := by
    have h1 := C.K_tail (1 / 2) (a - 1 / 4 - OffLinePairData.sh) (by norm_num)
    have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
    rw [hsh] at h1
    have h2 : expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) ≤
        expTail Φ (1 / 2 + 3 / 2 * ((2 * W : ℕ) : ℝ)) (a - 3 / 8) := by
      apply expTail_mono_weight superExpDecay_riemannPhiKernel
      push_cast; have : (0 : ℝ) ≤ W := Nat.cast_nonneg _; linarith
    have h3 := expTail_riemannPhiKernel_level_le ha W hlam
    rw [hsh]
    calc expTail C.K (1 / 2) (a - 3 / 8) ≤ 2 ^ W * expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) := h1
      _ ≤ 2 ^ W * εΦ := by rw [hεΦdef]; gcongr; exact h2.trans h3
  have hε0 : 0 ≤ expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := expTail_nonneg _ _ _
  have hcM0 := coeffMass_nonneg C.Q
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hMi0 : 0 ≤ Mi := by linarith
  unfold testTail
  calc 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - shw)
      ≤ 6 * ((W + 1) * Mi) * (2 ^ W * εΦ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) hε hε0
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hMi0))
    _ = _ := by rw [hεΦdef]; ring

/-- The norm bound of the cluster test in explicit form. -/
theorem normBound_le (hne : C.nodes.Nonempty) {Kp : ℝ} (hKp : 0 ≤ Kp) :
    C.normBound Kp ≤ 10 * Kp * (((windowCount C.t₀ + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀)) *
      (C.t₀ + 3) ^ 2 * max C.Bk 1) := by
  set W := windowCount C.t₀ with hWdef
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  rw [← hMidef]
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcosh : 1 + Real.cosh (heightPolarShift C.t₀ / 2) ≤ 5 / 2 := by
    have := (heightPolarShift_mem C.ht₀).2
    have h := cosh_le_exp_abs (heightPolarShift C.t₀ / 2)
    rw [abs_of_pos (by linarith [(heightPolarShift_mem C.ht₀).1])] at h
    have h2 : Real.exp (heightPolarShift C.t₀ / 2) ≤ 3 / 2 :=
      (Real.exp_le_exp.mpr (by unfold OffLinePairData.sh; linarith)).trans
        OffLinePairData.exp_sh_half_le
    linarith
  have hch0 : 0 ≤ 1 + Real.cosh (heightPolarShift C.t₀ / 2) := by
    have := Real.cosh_pos (heightPolarShift C.t₀ / 2); linarith
  have hcM0 := coeffMass_nonneg C.Q
  have hB := C.Bk_nonneg
  have hBm : C.Bk ≤ max C.Bk 1 := le_max_left _ _
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hMi0 : 0 ≤ Mi := by linarith
  have hT : (1 + (C.t₀ + 2)) ^ 2 = (C.t₀ + 3) ^ 2 := by ring
  unfold normBound
  rw [hT]
  have h1 : coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2)) ≤ ((W + 1) * Mi) * (5 / 2) :=
    mul_le_mul hcM hcosh hch0 (by positivity)
  have h2 : (C.t₀ + 3) ^ 2 * C.Bk ≤ (C.t₀ + 3) ^ 2 * max C.Bk 1 :=
    mul_le_mul_of_nonneg_left hBm (sq_nonneg _)
  calc 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
        ((C.t₀ + 3) ^ 2 * C.Bk)
      ≤ 4 * Kp * (((W + 1) * Mi) * (5 / 2)) * ((C.t₀ + 3) ^ 2 * max C.Bk 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
          (mul_nonneg (sq_nonneg _) hB) (by positivity)
    _ = 10 * Kp * ((W + 1) * Mi * (C.t₀ + 3) ^ 2 * max C.Bk 1) := by ring

/-- The two factors of the size of the cluster test at `ρ` are at most `nyquistSize ρ`. -/
theorem size_bounds {ρ : ℂ} (hCt : C.t₀ = ρ.im) (hCδ : C.δ₀ = ρ.re - 1 / 2) :
    1 ≤ nyquistSize ρ ∧
    ((windowCount C.t₀ + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀)) * 2 ^ windowCount C.t₀ ≤
      nyquistSize ρ ∧
    ((windowCount C.t₀ + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀)) * (C.t₀ + 3) ^ 2 *
      max C.Bk 1 ≤ nyquistSize ρ := by
  have hBk : C.Bk = 2 ^ windowCount C.t₀ * expTail Φ (3 / 2 * windowCount C.t₀) 0 := rfl
  have hMi1 := C.one_le_interpBound
  unfold nyquistSize
  rw [← hCt, ← hCδ, ← hBk]
  obtain ⟨p, hp⟩ : ∃ x, x = (2 : ℝ) ^ windowCount C.t₀ := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ x, x = ((windowCount C.t₀ : ℝ) + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀) :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ x, x = (C.t₀ + 3) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ x, x = max C.Bk 1 := ⟨_, rfl⟩
  rw [← hp, ← hX, ← hT, ← hBm]
  have hp1 : 1 ≤ p := by rw [hp]; exact one_le_pow₀ (by norm_num)
  have hX1 : 1 ≤ X := by
    rw [hX]
    have : (0 : ℝ) ≤ windowCount C.t₀ := Nat.cast_nonneg _
    exact one_le_mul_of_one_le_of_one_le (by linarith) hMi1
  have hT1 : 1 ≤ T := by rw [hT]; have := C.ht₀; nlinarith
  have hBm1 : 1 ≤ Bm := by rw [hBm]; exact le_max_right _ _
  have hBT : 1 ≤ Bm * T := one_le_mul_of_one_le_of_one_le hBm1 hT1
  refine ⟨?_, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hp1 hBm1) hX1) hT1
  · have e : p * Bm * X * T = (X * p) * (Bm * T) := by ring
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hBT
  · have e : p * Bm * X * T = (X * T * Bm) * p := by ring
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hp1

end ClusterSetup


/-- **The Nyquist inertia law.** There are absolute constants `K₀, K₁` with the following
property. Let `a ≥ 1` and let `T` be a finite set of zeros `ρ = β + it` of `ζ` with `β > ½`,
`t ≥ 101`, ordinates pairwise at least `3/2` apart, each satisfying `6 + 3N ≤ 2πe^{2X}`
(`X = a - 3/8`). Suppose every `nyquistSize ρ ≤ Λ`, every `nyquistTail a ρ ≤ τ`, and
`K₀ |T| e^{a/2} Λ² τ ≤ 1`. Then the level-`a` Weil form of `ζ` has a `|T|`-dimensional space of
polar-constrained tests on which `Re W(f, f) < -∫|f|²/(K₁ a |T| Λ²)`:

`|T| ≤ weilNegIndex ζ a (1/(K₁ a |T| Λ²))`.

No depth margin, no isolation of the zeros and no loss from the polar constraints enters: each
zero is resolved by the cluster test at its height, and disjoint reflection-closed node sets make
the Weil Gram matrix of these tests diagonally dominant. In logarithmic form the condition is
`πe^{2a-3/4} ≥ πt/2 + log|T| + O(log t (log log t + log 1/δ) + N a)` for all `ρ ∈ T`: below the
Nyquist height every off-line zero is a negative square of the finite-level Weil form. -/
theorem weilNegIndex_ge_card_offline_zeros :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {a Λ τ : ℝ} (T : Finset ℂ), 1 ≤ a →
      (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re ∧ 101 ≤ ρ.im ∧
        1 / 2 + 3 * (windowCount ρ.im : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) ∧
        nyquistSize ρ ≤ Λ ∧ nyquistTail a ρ ≤ τ) →
      (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 3 / 2 ≤ |ρ.im - σ.im|) →
      K₀ * T.card * Real.exp (a / 2) * Λ ^ 2 * τ ≤ 1 →
      T.card ≤ weilNegIndex zetaZeroConfig a (1 / (K₁ * a * T.card * Λ ^ 2)) := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hupper := zeta_weil_negative_index_le_of_local_count hA₀ hloc
  have hS := zeroSumZ_nonneg
  have hMθ : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  obtain ⟨cθ, hcθ⟩ : ∃ x, x = 80 * Mθ * Real.exp π + 1 := ⟨_, rfl⟩
  have hcθ1 : 1 ≤ cθ := by
    rw [hcθ]; have := Real.exp_pos π
    have : 0 ≤ 80 * Mθ * Real.exp π := by positivity
    linarith
  have hcθ0 : 0 ≤ cθ := by linarith
  obtain ⟨S, hSdef⟩ : ∃ x, x = zeroSumZ := ⟨_, rfl⟩
  rw [← hSdef] at hS
  have hKp0 : 0 ≤ Kp := by linarith
  refine ⟨4800 * (S + 1) * cθ * Kp, 1600 * Kp ^ 2,
    mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (by linarith),
    mul_pos (by norm_num) (pow_pos (by linarith) 2), ?_⟩
  intro a Λ τ T ha hT hsep hK
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp
  have ha0 : 0 ≤ a := by linarith
  have hn1 : (1 : ℝ) ≤ T.card := by exact_mod_cast hTne.card_pos
  have hex : ∀ i : T, ∃ C : ClusterSetup, C.t₀ = (i : ℂ).im ∧ C.δ₀ = (i : ℂ).re - 1 / 2 ∧
      ∃ ν ∈ C.nodes, (ν : ℂ) = i := fun i =>
    exists_clusterSetup_node (hT i i.2).1 (hT i i.2).2.1 (hT i i.2).2.2.1
  choose Cs hCt hCδ ν hνm hνe using hex
  have hne : ∀ i, (Cs i).nodes.Nonempty := fun i => ⟨ν i, hνm i⟩
  have hWt : ∀ i : T, windowCount (Cs i).t₀ = windowCount (i : ℂ).im := fun i => by rw [hCt i]
  -- `Λ ≥ 1` and `τ ≥ 0`
  obtain ⟨ρ₁, hρ₁⟩ := hTne
  have hΛ1 : 1 ≤ Λ :=
    ((Cs ⟨ρ₁, hρ₁⟩).size_bounds (hCt _) (hCδ _)).1.trans (hT ρ₁ hρ₁).2.2.2.2.1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hτ0 : 0 ≤ τ := by
    have h1 : 0 < nyquistTail a ρ₁ := Real.exp_pos _
    linarith [(hT ρ₁ hρ₁).2.2.2.2.2]
  have hcΛτ : 0 ≤ 6 * cθ * Λ * τ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcθ0) hΛ0) hτ0
  have h10 : 0 ≤ 10 * Kp * Λ := mul_nonneg (mul_nonneg (by norm_num) hKp0) hΛ0
  -- per-zero bounds
  have hη : ∀ i : T, (Cs i).testTail a ≤ 6 * cθ * Λ * τ := by
    intro i
    obtain ⟨-, -, -, h4, h5, h6⟩ := hT i i.2
    have hlam : 1 / 2 + 3 * (windowCount (Cs i).t₀ : ℝ) + 11 / 2 ≤
        2 * π * Real.exp (2 * (a - 3 / 8)) := by rw [hWt]; exact h4
    have ht := (Cs i).testTail_le (hne i) ha hlam
    obtain ⟨-, hsz, -⟩ := (Cs i).size_bounds (hCt i) (hCδ i)
    have htail : Real.exp ((1 / 2 + 3 * (windowCount (Cs i).t₀ : ℝ) + 9 / 2) * (a - 3 / 8) -
        π * Real.exp (2 * (a - 3 / 8))) ≤ τ := by rw [hWt]; exact h6
    rw [← hcθ] at ht
    refine ht.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hsz.trans h5)
      (mul_nonneg (by norm_num) hcθ0)) htail (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) hcθ0) hΛ0)
  have hB : ∀ i : T, (Cs i).normBound Kp ≤ 10 * Kp * Λ := by
    intro i
    obtain ⟨-, -, hsz⟩ := (Cs i).size_bounds (hCt i) (hCδ i)
    have h5 := (hT i i.2).2.2.2.2.1
    exact ((Cs i).normBound_le (hne i) hKp0).trans
      (mul_le_mul_of_nonneg_left (hsz.trans h5) (mul_nonneg (by norm_num) hKp0))
  have hprop := fun i : T => (Cs i).test_properties (hνm i) a hKp2 hKp
  have hN : ∀ i : T, (∫ u, ‖(Cs i).test a u‖) + (∫ u, ‖deriv (deriv ((Cs i).test a)) u‖) ≤
      10 * Kp * Λ := fun i => (hprop i).2.2.2.2.2.trans (hB i)
  have hN0 : ∀ i : T, 0 ≤ (∫ u, ‖(Cs i).test a u‖) := fun i =>
    integral_nonneg fun _ => norm_nonneg _
  have hN0' : ∀ i : T, 0 ≤ (∫ u, ‖deriv (deriv ((Cs i).test a)) u‖) := fun i =>
    integral_nonneg fun _ => norm_nonneg _
  -- the smallness parameter
  obtain ⟨P, hPdef⟩ : ∃ x, x = Real.exp (a / 2) * Λ ^ 2 * τ := ⟨_, rfl⟩
  have hea : 1 ≤ Real.exp (a / 2) := Real.one_le_exp (by linarith)
  have hP0 : 0 ≤ P := by rw [hPdef]; exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hτ0
  have hΛτ : Λ * τ ≤ P := by
    have h1 : Λ * τ ≤ Λ ^ 2 * τ := by
      apply mul_le_mul_of_nonneg_right _ hτ0; nlinarith
    have h2 : Λ ^ 2 * τ ≤ Real.exp (a / 2) * (Λ ^ 2 * τ) :=
      le_mul_of_one_le_left (mul_nonneg (sq_nonneg _) hτ0) hea
    rw [hPdef]; linarith
  set n : ℝ := (T.card : ℝ) with hn
  have hK' : 4800 * ((S * (cθ * Kp * P) * n) + (cθ * Kp * P) * n) ≤ 1 := by
    have e : 4800 * (S + 1) * cθ * Kp * n * Real.exp (a / 2) * Λ ^ 2 * τ =
        4800 * ((S * (cθ * Kp * P) * n) + (cθ * Kp * P) * n) := by rw [hPdef]; ring
    rw [← e]; exact hK
  have hR0 : 0 ≤ cθ * Kp * P := mul_nonneg (mul_nonneg hcθ0 hKp0) hP0
  have hRn : cθ * Kp * P ≤ cθ * Kp * P * n := le_mul_of_one_le_right hR0 hn1
  have hSR : 0 ≤ S * (cθ * Kp * P) := mul_nonneg hS hR0
  have hSRn : 0 ≤ S * (cθ * Kp * P) * n := by positivity
  have hηs : ∀ i : T, (Cs i).testTail a ≤ 1 / 4 := by
    intro i
    have h1 : cθ * (Λ * τ) ≤ cθ * P := mul_le_mul_of_nonneg_left hΛτ hcθ0
    have h2 : cθ * P ≤ cθ * Kp * P / 2 := by
      have : cθ * P * 2 ≤ cθ * P * Kp := mul_le_mul_of_nonneg_left hKp2 (mul_nonneg hcθ0 hP0)
      linarith
    have := hη i
    have e : 6 * cθ * Λ * τ = 6 * (cθ * (Λ * τ)) := by ring
    linarith
  -- the Gram data
  set D : ℝ := 300 * S * cθ * Kp * P with hD
  set O : ℝ := 600 * S * cθ * Kp * P with hO
  set M : ℝ := 200 * a * Kp ^ 2 * Λ ^ 2 with hM
  set ε : ℝ := 1 / (1600 * Kp ^ 2 * a * n * Λ ^ 2) with hε
  have hden : 0 < 1600 * Kp ^ 2 * a * n * Λ ^ 2 := by
    have : 0 < Kp := by linarith
    have : 0 < Λ := by linarith
    have : 0 < n := by linarith
    positivity
  have hε0 : 0 < ε := by rw [hε]; exact one_div_pos.mpr hden
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hden]
    have h1 : 1 ≤ Kp ^ 2 := by nlinarith
    have h2 : 1 ≤ Λ ^ 2 := by nlinarith
    have h3 : 1 ≤ Kp ^ 2 * a := one_le_mul_of_one_le_of_one_le h1 ha
    have h4 : 1 ≤ Kp ^ 2 * a * n := one_le_mul_of_one_le_of_one_le h3 hn1
    have h5 : 1 ≤ Kp ^ 2 * a * n * Λ ^ 2 := one_le_mul_of_one_le_of_one_le h4 h2
    linarith
  have hdiag : ∀ i : T, (zetaZeroConfig.W ((Cs i).test a) ((Cs i).test a)).re ≤ -(3 / 8) + D := by
    intro i
    have h := (Cs i).re_W_test_le (hνm i) ha0 hKp2 hKp (hηs i)
    rw [← hSdef] at h
    have hηB : (Cs i).testTail a * (Cs i).normBound Kp ≤ (6 * cθ * Λ * τ) * (10 * Kp * Λ) :=
      mul_le_mul (hη i) (hB i) ((Cs i).normBound_nonneg hKp0) hcΛτ
    have h2 := mul_le_mul_of_nonneg_left hηB
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hS) (Real.exp_pos (a / 2)).le)
    have e1 : 5 * S * (Cs i).testTail a * Real.exp (a / 2) * (Cs i).normBound Kp =
        5 * S * Real.exp (a / 2) * ((Cs i).testTail a * (Cs i).normBound Kp) := by ring
    have e2 : 5 * S * Real.exp (a / 2) * ((6 * cθ * Λ * τ) * (10 * Kp * Λ)) = D := by
      rw [hD, hPdef]; ring
    linarith
  have hoff : ∀ i j : T, i ≠ j →
      ‖zetaZeroConfig.W ((Cs i).test a) ((Cs j).test a)‖ ≤ O := by
    intro i j hij
    have hsep' : 3 / 2 ≤ |(Cs i).t₀ - (Cs j).t₀| := by
      rw [hCt, hCt]; exact hsep i i.2 j j.2 fun h => hij (Subtype.ext h)
    have h := norm_W_cluster_tests_le (Cs i) (Cs j) hsep' ha0 (hprop i).1 (hprop j).1
      (hprop i).2.1 (hprop j).2.1
    rw [← hSdef] at h
    have hE := (Real.exp_pos (a / 2)).le
    have t : ∀ k l : T, (Cs k).testTail a * (Real.exp (a / 2) *
        (4 * ((∫ u, ‖(Cs l).test a u‖) + ∫ u, ‖deriv (deriv ((Cs l).test a)) u‖))) ≤
        (6 * cθ * Λ * τ) * (Real.exp (a / 2) * (4 * (10 * Kp * Λ))) := by
      intro k l
      have hl := hN l
      have h0 : 0 ≤ Real.exp (a / 2) *
          (4 * ((∫ u, ‖(Cs l).test a u‖) + ∫ u, ‖deriv (deriv ((Cs l).test a)) u‖)) :=
        mul_nonneg hE (mul_nonneg (by norm_num) (add_nonneg (hN0 l) (hN0' l)))
      exact mul_le_mul (hη k) (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hl (by norm_num)) hE) h0 hcΛτ
    have t1 := t i j
    have t2 := t j i
    have hS54 : 0 ≤ (5 / 4) * S := by positivity
    have e : (5 / 4) * S * ((6 * cθ * Λ * τ) * (Real.exp (a / 2) * (4 * (10 * Kp * Λ))) +
        (6 * cθ * Λ * τ) * (Real.exp (a / 2) * (4 * (10 * Kp * Λ)))) = O := by
      rw [hO, hPdef]; ring
    calc ‖zetaZeroConfig.W ((Cs i).test a) ((Cs j).test a)‖ ≤ _ := h
      _ ≤ (5 / 4) * S * ((6 * cθ * Λ * τ) * (Real.exp (a / 2) * (4 * (10 * Kp * Λ))) +
          (6 * cθ * Λ * τ) * (Real.exp (a / 2) * (4 * (10 * Kp * Λ)))) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) hS54
      _ = O := e
  have hO0 : 0 ≤ O := by rw [hO]; nlinarith
  have hDO : D + ((Fintype.card T : ℝ) - 1) * O ≤ 1 / 8 := by
    rw [Fintype.card_coe, ← hn, hD, hO]
    have e : 300 * S * cθ * Kp * P + (n - 1) * (600 * S * cθ * Kp * P) =
        600 * (S * (cθ * Kp * P) * n) - 300 * (S * (cθ * Kp * P)) := by ring
    rw [e]
    have : 0 ≤ cθ * Kp * P * n := by positivity
    linarith
  have hMi : ∀ i : T, ∫ u, ‖(Cs i).test a u‖ ^ 2 ≤ M := by
    intro i
    have h := integral_norm_sq_le ha0 (hprop i).1 (hprop i).2.1
    obtain ⟨A1, hA1⟩ : ∃ x, x = ∫ u, ‖(Cs i).test a u‖ := ⟨_, rfl⟩
    obtain ⟨A2, hA2⟩ : ∃ x, x = ∫ u, ‖deriv (deriv ((Cs i).test a)) u‖ := ⟨_, rfl⟩
    rw [← hA1, ← hA2] at h
    have hs := hN i
    rw [← hA1, ← hA2] at hs
    have h1 : 0 ≤ A1 := by rw [hA1]; exact hN0 i
    have h2 : 0 ≤ A2 := by rw [hA2]; exact hN0' i
    have h3 : A2 * A1 ≤ (10 * Kp * Λ) ^ 2 := by
      have e : (A1 + A2) ^ 2 = A2 * A1 + (A1 ^ 2 + A1 * A2 + A2 ^ 2) := by ring
      have : A2 * A1 ≤ (A1 + A2) ^ 2 := by
        rw [e]
        exact le_add_of_nonneg_right
          (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg h1 h2)) (sq_nonneg _))
      exact this.trans (pow_le_pow_left₀ (add_nonneg h1 h2) hs 2)
    rw [hM]
    calc ∫ u, ‖(Cs i).test a u‖ ^ 2 ≤ 2 * a * A2 * A1 := h
      _ = 2 * a * (A2 * A1) := by ring
      _ ≤ 2 * a * (10 * Kp * Λ) ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith only [ha0])
      _ = 200 * a * Kp ^ 2 * Λ ^ 2 := by ring
  have hεM : ε * (Fintype.card T * M) ≤ 1 / 8 := by
    rw [Fintype.card_coe, ← hn, hε, hM, div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
    apply le_of_eq; ring
  obtain ⟨V, hVf, hdim, hV, hneg⟩ := exists_negative_subspace_of_gram (ι := T)
    (fun i => (Cs i).test a) (fun i => (hprop i).1) (fun i => (hprop i).2.2.1)
    (fun i => (hprop i).2.2.2.1) (fun i => (hprop i).2.2.2.2.1) hdiag hoff hO0 hDO hMi hε0.le hεM
  have hbdd : BddAbove {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
      Module.finrank ℂ V = n ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} := by
    refine ⟨(offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card, ?_⟩
    rintro m ⟨W, hWf, rfl, hW, hWneg⟩
    exact hupper a ε (by linarith) hε0 hε1 W hWf hW hWneg
  have hmem : Module.finrank ℂ V ∈ {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ),
      FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} :=
    ⟨V, hVf, rfl, hV, hneg⟩
  have hle := le_csSup hbdd hmem
  rw [hdim, Fintype.card_coe] at hle
  unfold weilNegIndex
  exact hle

end

end RHTower
