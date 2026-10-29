import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Attained depth is seen by almost every prime

The tower Hasse principle (`TowerFaithfulSpectraAreDecidedByAlmostEveryTower`) covers finitely many
pairs; fine towers (`FineTowersDecideEveryOrbitKernel`) cover every orbit kernel. For the coarse prime
towers and one test, with infinitely many zeros, positivity on a tower has to defeat the growth of the
deepest nodes against an infinite remainder. This module proves that it never can when the largest
depth `D = max (½ − Re ρ) > 0` is **attained**, by finitely or infinitely many zeros.

**Bohr coefficients along one tower** (`tsum_weight_node_eq_zero_of_bounded`). Along `u^n`,
`scale u > 0`, divide the orbit kernel `Σ_ρ W_ρ ν_ρ^n` by `R^n`, `R = e^{D·scale u}`: every normalized
node `z_ρ = ν_ρ / R` has `|z_ρ| ≤ 1`, with equality exactly at depth `D`. If the kernel is bounded
along the tower, the normalized kernel tends to `0`, and so do its Cesàro means against `w̄^n` for a
unimodular `w`. Termwise these means tend to `W_ρ` when `z_ρ = w` and to `0` otherwise
(`tendsto_cesaro_pow`), dominated by `|W_ρ|`, so by Tannery's theorem the total weight of the zeros
with node `R w` vanishes.

**Almost every prime** (`finite_primes_posDef_of_attained_depth`). Fix a zero `ρ₀` of depth `D` with
`W_{ρ₀} ≠ 0`. At a prime tower where the kernel is positive definite, hence bounded, `W_{ρ₀}` is
cancelled by the zeros aliasing with `ρ₀` there. A zero aliases with `ρ₀` at most at one prime
(`eq_of_alias_of_alias`), so these alias sets are disjoint, and a summable mass has only finitely many
disjoint pieces of size `≥ |W_{ρ₀}|` (`finite_of_disjoint_mass`).

**For `ζ`** (`zeta_finite_primes_posDef_of_attained_depth`): if the real parts of the zeros attain
their infimum and it is `< ½`, the Weil kernel is positive definite on only finitely many prime
towers. Hence RH is equivalent to positivity on infinitely many prime towers whenever the least real
part is attained (`riemannHypothesis_iff_infinite_primes_posDef_of_attained`); this contains the
finite-support stratum. What remains open is an infimum that is not attained.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests cx_contDiff cx_hasCompactSupport
  summable_norm_Wsummand)
open GaloisForLFunctions.ArithmeticOrientationGeometry (Sees sees_reflect seenRightZeros
  seenRightZeros_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

theorem logChar_neg_apply {G : Type*} [Group G] (ℓ : G →* Multiplicative ℝ) (s : ℂ) (u : G) :
    logChar ℓ (-s) u = (logChar ℓ s u)⁻¹ := by
  rw [logChar_apply, logChar_apply, neg_mul, Complex.exp_neg]

/-! ### Cesàro means of powers and disjoint masses -/

theorem norm_cesaro_pow_le {c : ℂ} (hc : ‖c‖ ≤ 1) (N : ℕ) :
    ‖(N : ℂ)⁻¹ * ∑ n ∈ range N, c ^ n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hsum : ‖∑ n ∈ range N, c ^ n‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range N, ‖c ^ n‖ ≤ ∑ _n ∈ range N, (1 : ℝ) :=
          sum_le_sum fun n _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
      _ = N := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, c ^ n‖ ≤ (N : ℝ)⁻¹ * N :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/-- **Cesàro means of a contracting power.** For `|c| ≤ 1`, `N⁻¹ Σ_{n<N} c^n → [c = 1]`. -/
theorem tendsto_cesaro_pow {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, c ^ n) atTop
      (𝓝 (if c = 1 then 1 else 0)) := by
  split_ifs with h1
  · subst h1
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact (inv_mul_cancel₀ (by exact_mod_cast (by omega : N ≠ 0))).symm
  · have hc1 : ‖c - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
    refine squeeze_zero_norm (a := fun N : ℕ => (N : ℝ)⁻¹ * (2 / ‖c - 1‖)) (fun N => ?_) ?_
    · rw [norm_mul, norm_inv, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg N))
      rw [geom_sum_eq h1, norm_div]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖c ^ N - 1‖ ≤ ‖c ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_pow, norm_one]
          exact add_le_add (pow_le_one₀ (norm_nonneg _) hc) le_rfl
        _ = 2 := by norm_num
    · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖c - 1‖)

/-- **Disjoint pieces of a finite mass.** If the sets `S p` are pairwise disjoint and `b ≥ 0` is
summable, only finitely many `S p` carry mass at least `c > 0`. -/
theorem finite_of_disjoint_mass {ι P : Type*} {S : P → Set ι}
    (hdisj : ∀ p q, p ≠ q → Disjoint (S p) (S q)) {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hb : Summable b) {c : ℝ} (hc : 0 < c) :
    {p | c ≤ ∑' i, (S p).indicator b i}.Finite := by
  classical
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊(∑' i, b i) / c⌋₊ + 1)
  have hsum : ∀ p, Summable ((S p).indicator b) := fun p => hb.indicator _
  -- at most one piece of `t` contains a given point
  have hpt : ∀ i, ∑ p ∈ t, (S p).indicator b i ≤ b i := fun i => by
    by_cases h : ∃ p ∈ t, i ∈ S p
    · obtain ⟨p, hp, hip⟩ := h
      rw [sum_eq_single p (fun q _ hqp => Set.indicator_of_notMem
          (Set.disjoint_left.mp (hdisj p q (Ne.symm hqp)) hip) _) (fun h => absurd hp h),
        Set.indicator_of_mem hip]
    · push Not at h
      rw [sum_eq_zero fun p hp => Set.indicator_of_notMem (h p hp) _]
      exact hb0 i
  have h1 : (t.card : ℝ) * c ≤ ∑' i, b i :=
    calc (t.card : ℝ) * c = ∑ _p ∈ t, c := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ t, ∑' i, (S p).indicator b i := sum_le_sum fun p hp => hts hp
      _ = ∑' i, ∑ p ∈ t, (S p).indicator b i :=
          (Summable.tsum_finsetSum fun p _ => hsum p).symm
      _ ≤ ∑' i, b i := Summable.tsum_le_tsum hpt (summable_sum fun p _ => hsum p) hb
  rw [htc] at h1
  have hfl := Nat.lt_floor_add_one ((∑' i, b i) / c)
  rw [div_lt_iff₀ hc] at hfl
  push_cast at h1
  linarith

/-! ### Bohr coefficients along one tower -/

section AttainedDepth

variable {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ} (hf : f ∈ realTests) {D : ℝ}
  (hD : 0 < D) (hmax : ∀ ρ ∈ Z.carrier, 1 / 2 - ρ.re ≤ D)
include hZ hf hD hmax

/-- **The top Bohr coefficients of a bounded tower vanish.** If the orbit kernel is bounded along
`u^n`, `scale u > 0`, then for every `v` of modulus `R = e^{D·scale u}` the total weight of the zeros
with node `ν_ρ(u) = v` is `0`. -/
theorem tsum_weight_node_eq_zero_of_bounded {u : HeckeLattice} (hu : 0 < scale heckeLogScale u)
    (hB : ∃ B : ℝ, ∀ n : ℕ, ‖orbitKernel Z f (u ^ n)‖ ≤ B) {v : ℂ}
    (hv : ‖v‖ = Real.exp (D * scale heckeLogScale u)) :
    ∑' ρ : Z.carrier, (if logChar heckeLogScale (1 / 2 - (ρ : ℂ)) u = v then
      Z.Wsummand (cx f) (cx f) ρ else 0) = 0 := by
  classical
  obtain ⟨B, hB⟩ := hB
  set s := scale heckeLogScale u with hs
  set W : ℂ → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ with hWdef
  set ν : ℂ → ℂ := fun ρ => logChar heckeLogScale (1 / 2 - ρ) u with hνdef
  set R := Real.exp (D * s) with hRdef
  have hR1 : 1 < R := Real.one_lt_exp_iff.mpr (mul_pos hD hu)
  have hRpos : 0 < R := zero_lt_one.trans hR1
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  set z : ℂ → ℂ := fun ρ => ν ρ / R with hzdef
  have hnorm : ∀ ρ, ‖ν ρ‖ = Real.exp ((1 / 2 - ρ.re) * s) := fun ρ => by
    simp only [hνdef, norm_logChar, sub_re, one_div, inv_re, normSq_ofNat]
    norm_num [hs]
  have hzle : ∀ ρ ∈ Z.carrier, ‖z ρ‖ ≤ 1 := fun ρ hρ => by
    rw [hzdef, norm_div, hnorm, Complex.norm_real, Real.norm_of_nonneg hRpos.le,
      div_le_one hRpos]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hmax ρ hρ) hu.le)
  -- the reference frequency `w' = R / v`
  have hv0 : v ≠ 0 := fun h => by rw [h, norm_zero] at hv; exact hRpos.ne' hv.symm
  set w' : ℂ := (R : ℂ) / v with hw'def
  have hw' : ‖w'‖ = 1 := by
    rw [hw'def, norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le, hv, div_self hRpos.ne']
  have hzw : ∀ ρ ∈ Z.carrier, ‖z ρ * w'‖ ≤ 1 := fun ρ hρ => by
    rw [norm_mul, hw', mul_one]; exact hzle ρ hρ
  have hsumW := summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  -- the normalized kernel as a series
  have hterm : ∀ (n : ℕ) (ρ : ℂ), orbitTerm Z f (u ^ n) ρ = W ρ * ν ρ ^ n := fun n ρ => by
    simp only [orbitTerm, map_pow, hWdef, hνdef]; ring
  have hser : ∀ n : ℕ, orbitKernel Z f (u ^ n) / (R : ℂ) ^ n * w' ^ n =
      ∑' ρ : Z.carrier, W ρ * (z ρ * w') ^ n := fun n => by
    rw [orbitKernel_eq_tsum, ← tsum_div_const, ← tsum_mul_right]
    refine tsum_congr fun ρ => ?_
    rw [hterm]
    simp only [hzdef, mul_pow, div_pow]
    field_simp
  have hsumn : ∀ n : ℕ, Summable fun ρ : Z.carrier => W ρ * (z ρ * w') ^ n := fun n =>
    Summable.of_norm_bounded hsumW fun ρ => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hzw ρ ρ.2))
  -- bounded along the tower: the normalized kernel tends to `0`, and so do its Cesàro means
  have hK : Tendsto (fun n : ℕ => orbitKernel Z f (u ^ n) / (R : ℂ) ^ n * w' ^ n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => B * (R⁻¹) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hRpos.le)
        (inv_lt_one_of_one_lt₀ hR1)).const_mul B
    refine squeeze_zero_norm (fun n => ?_) hlim
    rw [norm_mul, norm_pow w', hw', one_pow, mul_one, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hRpos.le, div_eq_mul_inv, inv_pow]
    exact mul_le_mul_of_nonneg_right (hB n) (by positivity)
  have hC : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, orbitKernel Z f (u ^ n) / (R : ℂ) ^ n * w' ^ n) atTop (𝓝 0) := by
    refine (hK.cesaro_smul).congr fun N => ?_
    rw [Complex.real_smul]
    push_cast
    rfl
  -- termwise, the Cesàro means converge to the coefficient at `w'⁻¹`
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (ρ : Z.carrier) => W ρ * ((N : ℂ)⁻¹ * ∑ n ∈ range N, (z ρ * w') ^ n))
    (g := fun ρ : Z.carrier => W ρ * (if z ρ * w' = 1 then 1 else 0)) (bound := fun ρ => ‖W ρ‖)
    hsumW (fun ρ => (tendsto_cesaro_pow (hzw ρ ρ.2)).const_mul (W ρ))
    (Eventually.of_forall fun N ρ => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_cesaro_pow_le (hzw ρ ρ.2) N))
  have hsame : ∀ N : ℕ, ∑' ρ : Z.carrier, W ρ * ((N : ℂ)⁻¹ * ∑ n ∈ range N, (z ρ * w') ^ n) =
      (N : ℂ)⁻¹ * ∑ n ∈ range N, orbitKernel Z f (u ^ n) / (R : ℂ) ^ n * w' ^ n := fun N => by
    simp_rw [hser]
    rw [← Summable.tsum_finsetSum fun n _ => hsumn n, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hzero : ∑' ρ : Z.carrier, W ρ * (if z ρ * w' = 1 then 1 else 0) = 0 :=
    tendsto_nhds_unique (hT.congr hsame) hC
  refine (tsum_congr fun ρ => ?_).trans hzero
  have hzv : z ρ * w' = ν ρ / v := by rw [hzdef, hw'def]; field_simp
  simp only [hzv, div_eq_one_iff_eq hv0, hνdef, hWdef]
  split_ifs <;> simp

/-- **A tower with a nonzero top coefficient sees a negative square.** -/
theorem not_isPosDefKernel_of_node_weight_ne_zero {u : HeckeLattice}
    (hu : 0 < scale heckeLogScale u) {v : ℂ} (hv : ‖v‖ = Real.exp (D * scale heckeLogScale u))
    (hne : ∑' ρ : Z.carrier, (if logChar heckeLogScale (1 / 2 - (ρ : ℂ)) u = v then
      Z.Wsummand (cx f) (cx f) ρ else 0) ≠ 0) :
    ¬ IsPosDefKernel (orbitKernel Z f ∘ zpowersHom _ u) := fun hpd =>
  hne (tsum_weight_node_eq_zero_of_bounded hZ hf hD hmax hu
    ⟨((orbitKernel Z f ∘ zpowersHom _ u) 1).re, fun n => by
      have := hpd.norm_le (Multiplicative.ofAdd (n : ℤ))
      simpa [zpowersHom_apply] using this⟩ hv)

/-- **Almost every prime tower sees an attained depth.** If a zero `ρ₀` of maximal depth `D > 0`
has nonzero weight, the orbit kernel is positive definite on only finitely many prime towers. -/
theorem finite_primes_posDef_of_attained_depth {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hdep : 1 / 2 - ρ₀.re = D) (hW₀ : Z.Wsummand (cx f) (cx f) ρ₀ ≠ 0) :
    {p : Nat.Primes | IsPosDefKernel (orbitKernel Z f ∘ zpowersHom _ (primeElt p.2))}.Finite := by
  classical
  set W : ℂ → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ with hWdef
  -- the zeros aliasing with `ρ₀` at `p`: disjoint over the primes
  set A : Nat.Primes → Set Z.carrier := fun p =>
    {ρ | (ρ : ℂ) ≠ ρ₀ ∧ zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2)} with hAdef
  have hdisj : ∀ p q, p ≠ q → Disjoint (A p) (A q) := fun p q hpq =>
    Set.disjoint_left.mpr fun ρ hp hq =>
      hpq (Subtype.ext (eq_of_alias_of_alias hp.1 p.2 q.2 hp.2 hq.2))
  have hsumW := summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  refine (finite_of_disjoint_mass hdisj (b := fun ρ : Z.carrier => ‖W ρ‖) (fun _ => norm_nonneg _)
    hsumW (norm_pos_iff.mpr hW₀)).subset fun p hp => ?_
  -- at a positive tower the alias set of `p` cancels the weight of `ρ₀`
  have hlog : 0 < scale heckeLogScale (primeElt p.2) := by
    rw [scale_primeElt]; exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  set v := logChar heckeLogScale (1 / 2 - ρ₀) (primeElt p.2) with hvdef
  have hv : ‖v‖ = Real.exp (D * scale heckeLogScale (primeElt p.2)) := by
    rw [hvdef, norm_logChar, ← hdep]
    norm_num
  have hzero := tsum_weight_node_eq_zero_of_bounded hZ hf hD hmax hlog
    ⟨((orbitKernel Z f ∘ zpowersHom _ (primeElt p.2)) 1).re, fun n => by
      have := (show IsPosDefKernel _ from hp).norm_le (Multiplicative.ofAdd (n : ℤ))
      simpa [zpowersHom_apply] using this⟩ hv
  have hνinv : ∀ ρ : ℂ, logChar heckeLogScale (1 / 2 - ρ) (primeElt p.2) =
      (zeroChar ρ (primeElt p.2))⁻¹ := fun ρ => by
    show _ = (logChar heckeLogScale (ρ - 1 / 2) (primeElt p.2))⁻¹
    rw [← logChar_neg_apply, neg_sub]
  have hcond : ∀ ρ : ℂ, logChar heckeLogScale (1 / 2 - ρ) (primeElt p.2) = v ↔
      zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2) := fun ρ => by
    rw [hvdef, hνinv, hνinv, inv_inj]
  have hsplit : ∀ ρ : Z.carrier,
      (if logChar heckeLogScale (1 / 2 - (ρ : ℂ)) (primeElt p.2) = v then W ρ else 0) =
        (if ρ = ⟨ρ₀, hρ₀⟩ then W ρ₀ else 0) + (A p).indicator (fun ρ : Z.carrier => W ρ) ρ :=
    fun ρ => by
      by_cases h0 : ρ = ⟨ρ₀, hρ₀⟩
      · subst h0
        rw [if_pos rfl, if_pos rfl, Set.indicator_of_notMem (fun h => h.1 rfl), add_zero]
      · have h0' : (ρ : ℂ) ≠ ρ₀ := fun h => h0 (Subtype.ext h)
        rw [if_neg h0, zero_add]
        by_cases ha : zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2)
        · rw [if_pos ((hcond ρ).mpr ha), Set.indicator_of_mem (show ρ ∈ A p from ⟨h0', ha⟩)]
        · rw [if_neg fun h => ha ((hcond ρ).mp h),
            Set.indicator_of_notMem (show ρ ∉ A p from fun h => ha h.2)]
  have hsumI : Summable ((A p).indicator fun ρ : Z.carrier => W ρ) :=
    (hsumW.of_norm).indicator _
  have hsum0 : Summable fun ρ : Z.carrier => if ρ = ⟨ρ₀, hρ₀⟩ then W ρ₀ else 0 :=
    (hasSum_ite_eq _ _).summable
  rw [tsum_congr hsplit, hsum0.tsum_add hsumI, tsum_ite_eq] at hzero
  show ‖W ρ₀‖ ≤ ∑' ρ, (A p).indicator (fun ρ : Z.carrier => ‖W ρ‖) ρ
  rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
  refine (norm_tsum_le_tsum_norm hsumI.norm).trans (le_of_eq (tsum_congr fun ρ => ?_))
  exact norm_indicator_eq_indicator_norm (f := fun ρ : Z.carrier => W ρ) (a := ρ)

end AttainedDepth

/-! ### The Weil kernel of `ζ` -/

/-- The cubic spline sees every zero of `ζ` off the critical line. -/
theorem zeta_Wsummand_ne_zero_of_left {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : ρ.re < 1 / 2) :
    zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ ≠ 0 := by
  have hR : reflect ρ ∈ seenRightZeros zetaZeroConfig cubicSpline := by
    rw [seenRightZeros_cubicSpline]
    exact ⟨zetaZeroConfig.reflect_mem ρ hρ, by simp [reflect]; linarith⟩
  have hs : Sees cubicSpline ρ := by
    have := sees_reflect hR.2.2
    rwa [show reflect (reflect ρ) = ρ by simp [reflect]] at this
  obtain ⟨h1, h2⟩ := hs
  simp only [ZeroConfig.Wsummand]
  refine mul_ne_zero (mul_ne_zero ?_ h1) ((_root_.map_ne_zero _).mpr h2)
  have := zetaZeroConfig.one_le_mult ρ hρ
  exact_mod_cast (by omega : zetaZeroConfig.mult ρ ≠ 0)

/-- **For `ζ`: an attained infimum of the real parts below `½` fails positivity on almost every
prime tower.** If some zero `ρ₀` with `Re ρ₀ < ½` has the least real part among all zeros, the Weil
kernel is positive definite on only finitely many prime towers. -/
theorem zeta_finite_primes_posDef_of_attained_depth {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hre : ρ₀.re < 1 / 2)
    (hmin : ∀ ρ ∈ zetaZeroConfig.carrier, ρ₀.re ≤ ρ.re) :
    {p : Nat.Primes | IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt p.2))}.Finite :=
  finite_primes_posDef_of_attained_depth temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
    (D := 1 / 2 - ρ₀.re) (by linarith) (fun ρ hρ => by have := hmin ρ hρ; linarith) hρ₀ rfl
    (zeta_Wsummand_ne_zero_of_left hρ₀ hre)

/-- **Infinitely many prime towers decide RH whenever the least real part is attained.** If every
zero left of the line lies above a zero of least real part, then RH holds iff the Weil kernel is
positive definite on infinitely many prime towers. -/
theorem riemannHypothesis_iff_infinite_primes_posDef_of_attained
    (hatt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 / 2 →
      ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ₀.re ≤ ρ'.re) :
    RiemannHypothesis ↔
      {p : Nat.Primes | IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt p.2))}.Infinite := by
  constructor
  · intro hRH
    have hpos := (isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH)
    exact Set.infinite_univ.mono fun p _ => hpos.comp _
  · intro hinf
    by_contra hRH
    rw [ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_rightZeros_zeta_eq_empty] at hRH
    obtain ⟨σ, hσ, hσre⟩ := Set.nonempty_iff_ne_empty.mpr hRH
    -- the reflection of a right zero lies left of the line
    have hl : reflect σ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem σ hσ
    have hlre : (reflect σ).re < 1 / 2 := by simp [reflect]; linarith
    obtain ⟨ρ₀, hρ₀, hmin⟩ := hatt _ hl hlre
    exact hinf (zeta_finite_primes_posDef_of_attained_depth hρ₀ ((hmin _ hl).trans_lt hlre) hmin)

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms riemannHypothesis_iff_infinite_primes_posDef_of_attained
