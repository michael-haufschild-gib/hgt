import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.HeckeKreinToeplitz.OnTheFiniteStratumEveryFlipHasInfiniteIndex
import GaloisForLFunctions.RHTower.OddWeilGramLimit
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingBoundForFlipTwins

/-!
# Flip twins carry their index into the coupling form

A flip twin keeps the pole and Gamma terms of `ζ` and changes the prime weights `Λ` to `λ`. Its
Weil kernel `K_λ(u) = W_λ(f, T_{log u} f)` (`weightKernel`) is not the orbit kernel of a zero
configuration, so the visibility argument of `MixedDifferencesSeeEveryZero` does not apply. The
coupling Laplacian still acts on the test side:

* **Differences on the test side** (`weightKernel_diffTest`, `weightKernel_mixedDiff`): for every
  weight `λ`, the kernel of the difference test `h(· − log a) − h` is `L_a K_λ`, and the kernel of
  the mixed difference is `L_a L_b K_λ`. The Weil functional is linear, the correlation is
  sesquilinear, and translating both tests shifts the correlation by their difference.
  Hence the coupling index of a twin is the kernel index of the twin on mixed-difference tests
  (`negIndex_lap_lap_weightKernel`).
* **Coupling selectivity against flips** (`negIndex_lap_lap_zeta_eq_top_or_flip`). Let `f` be a
  nonzero real test supported in `[−A, A]` and let the scales satisfy `log a, log b > 0` with
  `2(A + log a + log b) ≤ log p`. Then the coupling forms `L_a L_b K_ζ` and `L_a L_b K_λ` of `ζ` and
  of its `p`-flip twin never both have finite index. The mixed difference of `f` is again a
  nonzero test supported in `[−A − log a − log b, A + log a + log b]`, so the corpus theorem
  `negIndex_zetaKernel_eq_top_or_flip` applies to it; and `κ(L_a L_b K_ζ) = κ(K_ζ)`.

On the finite stratum (finitely many off-line zeros) the coupling form of `ζ` has finite index, so
the coupling form of every single-prime flip twin has infinitely many negative squares
(`negIndex_lap_lap_flip_eq_top_of_finite`).

* **Flip sets of every density** (`coupling_primeSetFlip_sub_coupling_zeta`). For an arbitrary set
  of primes `P` and a test supported in `[−a, a]` with `2a ≤ log(1 + 1/p²)`, the window around
  `p` and `p²` contains no other integer. So the `(p, p)`-coupling of the `P`-flip twin differs from
  that of `ζ` by exactly `−4 log p ‖f‖²/√p` if `p ∈ P`, and by `0` otherwise. The diagonal coupling
  recovers the flip set prime by prime (`mem_iff_coupling_primeSetFlip_ne`), whatever its density.
-/

open Complex Finset
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests rightZeros)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The difference test `h(· − δ) − h`. -/
def diffTest (δ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun x => h (x - δ) - h x

theorem diffTest_mem_realTests {h : ℝ → ℝ} (hh : h ∈ realTests) (δ : ℝ) :
    diffTest δ h ∈ realTests := by
  rw [show diffTest δ h = (fun x => h (x - δ)) - h from funext fun x => rfl]
  exact realTests.sub_mem (shift_mem_realTests hh δ) hh

theorem mixedDiff_eq_diffTest (α β : ℝ) (f : ℝ → ℝ) :
    mixedDiff α β f = diffTest α (diffTest β f) := by
  funext x; simp only [mixedDiff, diffTest, sub_sub]; ring

theorem cx_diffTest (δ : ℝ) (h : ℝ → ℝ) :
    cx (diffTest δ h) = ArithmeticCastelnuovoSeveri.translate δ (cx h) - cx h := by
  funext x; simp [cx, diffTest, ArithmeticCastelnuovoSeveri.translate]

/-- The correlation is sesquilinear in differences of continuous compactly supported tests. -/
theorem weilTest_sub_sub {f₁ f₂ g₁ g₂ : ℝ → ℂ} (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁)
    (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) (k₁ : Continuous g₁) (k₂ : Continuous g₂) :
    EF.weilTest (f₁ - f₂) (g₁ - g₂) =
      EF.weilTest f₁ g₁ - EF.weilTest f₁ g₂ - EF.weilTest f₂ g₁ + EF.weilTest f₂ g₂ := by
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, RHTower.WeilSpectral.weilTest_apply]
  have i11 := RHTower.WeilSpectral.integrable_mul_conj_shift h₁ h₁c k₁ x
  have i12 := RHTower.WeilSpectral.integrable_mul_conj_shift h₁ h₁c k₂ x
  have i21 := RHTower.WeilSpectral.integrable_mul_conj_shift h₂ h₂c k₁ x
  have i22 := RHTower.WeilSpectral.integrable_mul_conj_shift h₂ h₂c k₂ x
  have e : (fun u => (f₁ u - f₂ u) * conj (g₁ (u - x) - g₂ (u - x))) = fun u =>
      f₁ u * conj (g₁ (u - x)) - f₁ u * conj (g₂ (u - x)) - f₂ u * conj (g₁ (u - x)) +
        f₂ u * conj (g₂ (u - x)) := by
    funext u; simp only [map_sub]; ring
  have i1 : MeasureTheory.Integrable fun u =>
      f₁ u * conj (g₁ (u - x)) - f₁ u * conj (g₂ (u - x)) := i11.sub i12
  have i2 : MeasureTheory.Integrable fun u =>
      f₁ u * conj (g₁ (u - x)) - f₁ u * conj (g₂ (u - x)) - f₂ u * conj (g₁ (u - x)) := i1.sub i21
  rw [e, MeasureTheory.integral_add i2 i22, MeasureTheory.integral_sub i1 i21,
    MeasureTheory.integral_sub i11 i12]

/-- Translating both tests shifts the correlation by their difference. -/
theorem weilTest_translate_eq (g : ℝ → ℂ) (a b : ℝ) :
    EF.weilTest (ArithmeticCastelnuovoSeveri.translate a g) (ArithmeticCastelnuovoSeveri.translate b g) =
      EF.weilTest g (ArithmeticCastelnuovoSeveri.translate (b - a) g) := by
  funext u
  have h0 : ArithmeticCastelnuovoSeveri.translate 0 g = g := by
    funext v; simp [ArithmeticCastelnuovoSeveri.translate]
  have h := ArithmeticCastelnuovoSeveri.weilTest_translate 0 (b - a) g g u
  rw [h0] at h
  rw [ArithmeticCastelnuovoSeveri.weilTest_translate, h]
  congr 1; ring

theorem translate_translate (s t : ℝ) (g : ℝ → ℂ) :
    ArithmeticCastelnuovoSeveri.translate t (ArithmeticCastelnuovoSeveri.translate s g) =
      ArithmeticCastelnuovoSeveri.translate (s + t) g := by
  funext u; simp only [ArithmeticCastelnuovoSeveri.translate, sub_sub, add_comm t s]

/-- The correlation of a test with its translate by `s`. -/
def corrAt (g : ℝ → ℂ) (s : ℝ) : ℝ → ℂ := EF.weilTest g (ArithmeticCastelnuovoSeveri.translate s g)

/-- The correlation of a difference test with its `t`-translate is a second difference in `t`. -/
theorem weilTest_diffTest (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) (δ t : ℝ) :
    EF.weilTest (ArithmeticCastelnuovoSeveri.translate δ g - g)
        (ArithmeticCastelnuovoSeveri.translate t (ArithmeticCastelnuovoSeveri.translate δ g - g)) =
      corrAt g t - corrAt g (t - δ) - corrAt g (t + δ) + corrAt g t := by
  have hT : ∀ s, Continuous (ArithmeticCastelnuovoSeveri.translate s g) := fun s =>
    hg.comp (continuous_id.sub continuous_const)
  have hTc : ∀ s, HasCompactSupport (ArithmeticCastelnuovoSeveri.translate s g) := fun s =>
    hgc.comp_homeomorph (Homeomorph.subRight s)
  have hshift : ArithmeticCastelnuovoSeveri.translate t
      (ArithmeticCastelnuovoSeveri.translate δ g - g) =
      ArithmeticCastelnuovoSeveri.translate (δ + t) g - ArithmeticCastelnuovoSeveri.translate t g := by
    rw [← translate_translate]; rfl
  rw [hshift, weilTest_sub_sub (hT δ) (hTc δ) hg hgc (hT (δ + t)) (hT t),
    weilTest_translate_eq, weilTest_translate_eq, add_sub_cancel_left, add_comm δ t]
  rfl

/-- **The kernel of a difference test is the second difference of the kernel**, for every weight. -/
theorem weightKernel_diffTest (lam : ℕ → ℝ) {h : ℝ → ℝ} (hh : h ∈ realTests) (a : HeckeLattice) :
    weightKernel lam (diffTest (scale heckeLogScale a) h) = lap a (weightKernel lam h) := by
  funext w
  have hg := ArithmeticCastelnuovoSeveri.cx_contDiff hh.1
  have hgc := ArithmeticCastelnuovoSeveri.cx_hasCompactSupport hh.2
  have hΨ : ∀ s, RHTower.WeilSpectral.Admissible (corrAt (cx h) s) := fun s =>
    RHTower.OddResolvent.admissible_weilTest_mixed hg hgc
      (ArithmeticCastelnuovoSeveri.translate_contDiff hg s)
      (ArithmeticCastelnuovoSeveri.translate_hasCompactSupport hgc s)
  have hK : ∀ v : HeckeLattice, weightKernel lam h v =
      RHTower.weilFullFunctional lam (corrAt (cx h) (scale heckeLogScale v)) := fun v => rfl
  set δ := scale heckeLogScale a
  set t := scale heckeLogScale w
  have hsub : ∀ k₁ k₂ : ℝ → ℂ, k₁ - k₂ = k₁ + (-1 : ℂ) • k₂ := fun k₁ k₂ => by
    funext x; simp [sub_eq_add_neg]
  have a1 := hΨ t
  have a2 := (hΨ (t - δ)).smul (-1)
  have a3 := (hΨ (t + δ)).smul (-1)
  have hlhs : weightKernel lam (diffTest δ h) w = RHTower.weilFullFunctional lam
      (corrAt (cx h) t - corrAt (cx h) (t - δ) - corrAt (cx h) (t + δ) + corrAt (cx h) t) := by
    rw [← weilTest_diffTest (cx h) hg.continuous hgc δ t, ← cx_diffTest]; rfl
  rw [hlhs, hsub, hsub,
    RHTower.WeilSpectral.weilFullFunctional_add lam ((a1.add a2).add a3) (hΨ t),
    RHTower.WeilSpectral.weilFullFunctional_add lam (a1.add a2) a3,
    RHTower.WeilSpectral.weilFullFunctional_add lam a1 a2,
    RHTower.WeilSpectral.weilFullFunctional_smul, RHTower.WeilSpectral.weilFullFunctional_smul,
    lap, hK, hK, hK, scale_mul, scale_mul, scale_inv, ← sub_eq_add_neg]
  ring

/-- **The kernel of a mixed difference is the coupling Laplacian of the kernel**, for every
weight. -/
theorem weightKernel_mixedDiff (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : f ∈ realTests) (a b : HeckeLattice) :
    weightKernel lam (mixedDiff (scale heckeLogScale a) (scale heckeLogScale b) f) =
      lap a (lap b (weightKernel lam f)) := by
  rw [mixedDiff_eq_diffTest, weightKernel_diffTest lam (diffTest_mem_realTests hf _),
    weightKernel_diffTest lam hf]

/-- **The coupling index of a twin is a kernel index.** For every weight, the coupling form of the
kernel of `f` has the index of the kernel of the mixed difference of `f`. -/
theorem negIndex_lap_lap_weightKernel (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : f ∈ realTests)
    (a b : HeckeLattice) :
    negIndex (lap a (lap b (weightKernel lam f))) =
      negIndex (weightKernel lam (mixedDiff (scale heckeLogScale a) (scale heckeLogScale b) f)) := by
  rw [weightKernel_mixedDiff lam hf]

/-- A nonzero compactly supported function is not killed by a nonzero difference. -/
theorem diffTest_ne_zero {h : ℝ → ℝ} (hhc : HasCompactSupport h) {δ : ℝ} (hδ : δ ≠ 0)
    (hne : h ≠ 0) : diffTest δ h ≠ 0 := by
  intro h0
  apply hne
  have hper : Function.Periodic h δ := fun x => by
    have := congrFun h0 (x + δ)
    simp only [diffTest, add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall 0
  funext x
  by_contra hx
  -- push `x` far out along the period
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + |x|) / |δ|)
  have hδa : 0 < |δ| := abs_pos.mpr hδ
  have hfar : h (x + n * δ) ≠ 0 := by rw [hper.nat_mul n x]; exact hx
  have hmem := hR (subset_tsupport h hfar)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  have hnδ : R + |x| < n * |δ| := by rwa [div_lt_iff₀ hδa] at hn
  have : n * |δ| ≤ |x + n * δ| + |x| := by
    have := abs_sub_abs_le_abs_sub (n * δ) (-x)
    rw [abs_mul, Nat.abs_cast, abs_neg, sub_neg_eq_add, add_comm] at this
    linarith
  linarith

theorem integral_sq_pos_of_ne_zero {h : ℝ → ℝ} (hh : h ∈ realTests) (hne : h ≠ 0) :
    0 < ∫ u, h u ^ 2 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    (hh.1.continuous.pow 2) (hh.2.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)) (fun u => sq_nonneg _) (pow_ne_zero 2 hx)

/-- **The coupling forms of `ζ` and of a flip twin never both have finite index.** -/
theorem negIndex_lap_lap_zeta_eq_top_or_flip {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ} (hf : f ∈ realTests)
    (hM : 0 < ∫ u, f u ^ 2) {A : ℝ} (hsupp : ∀ u, A ≤ |u| → f u = 0)
    {a b : HeckeLattice} (ha : 0 < scale heckeLogScale a) (hb : 0 < scale heckeLogScale b)
    (hab : 2 * (A + scale heckeLogScale a + scale heckeLogScale b) ≤ Real.log p) :
    negIndex (lap a (lap b zetaKernel)) = ⊤ ∨
      negIndex (lap a (lap b (weightKernel (ArithmeticCountingPositivity.primeFlipWeight p) f))) = ⊤ := by
  have hA : 0 ≤ A := by
    by_contra hneg
    have hf0 : f = 0 := funext fun u => hsupp u ((not_le.mp hneg).le.trans (abs_nonneg u))
    rw [hf0] at hM; simp at hM
  have ha1 : a ≠ 1 := fun h1 => by simp [h1, scale] at ha
  have hb1 : b ≠ 1 := fun h1 => by simp [h1, scale] at hb
  set α := scale heckeLogScale a
  set β := scale heckeLogScale b
  set f' := mixedDiff α β f
  have hf' : f' ∈ realTests := mixedDiff_mem_realTests hf α β
  have hne : f ≠ 0 := by
    rintro rfl; simp at hM
  have hne' : f' ≠ 0 := by
    rw [show f' = diffTest α (diffTest β f) from mixedDiff_eq_diffTest α β f]
    exact diffTest_ne_zero (diffTest_mem_realTests hf β).2 ha.ne'
      (diffTest_ne_zero hf.2 hb.ne' hne)
  have hM' := integral_sq_pos_of_ne_zero hf' hne'
  have hsupp' : ∀ u, A + α + β ≤ |u| → f' u = 0 := fun u hu => by
    have h1 : ∀ s : ℝ, 0 ≤ s → s ≤ α + β → A ≤ |u - s| := fun s hs0 hs => by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h] at hu
        rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos h] at hu
        rw [abs_of_nonpos (by linarith)]; linarith
    have hz : ∀ s : ℝ, 0 ≤ s → s ≤ α + β → f (u - s) = 0 := fun s hs0 hs =>
      hsupp _ (h1 s hs0 hs)
    have h0 : f u = 0 := by simpa using hz 0 le_rfl (by linarith)
    simp only [f', mixedDiff]
    rw [sub_sub u α β, hz _ (by linarith) le_rfl, hz α ha.le (by linarith),
      hz β hb.le (by linarith), h0]
    ring
  have hcorpus := negIndex_zetaKernel_eq_top_or_flip hp hf' hM' hsupp' hab
  rcases hcorpus with h | h
  · left; rw [negIndex_lap_lap_zetaKernel ha1 hb1]; exact h
  · right; rw [← weightKernel_mixedDiff _ hf]; exact h

/-- **On the finite stratum every flip twin has infinite coupling index.** If `ζ` has finitely
many right zeros, the coupling form of every single-prime flip twin has infinitely many negative
squares, while that of `ζ` has exactly `#{right zeros}`. -/
theorem negIndex_lap_lap_flip_eq_top_of_finite {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hM : 0 < ∫ u, f u ^ 2) {A : ℝ}
    (hsupp : ∀ u, A ≤ |u| → f u = 0) {a b : HeckeLattice} (ha : 0 < scale heckeLogScale a)
    (hb : 0 < scale heckeLogScale b)
    (hab : 2 * (A + scale heckeLogScale a + scale heckeLogScale b) ≤ Real.log p)
    (hR : (rightZeros Zeta23.zetaZeroConfig).Finite) :
    negIndex (lap a (lap b (weightKernel (ArithmeticCountingPositivity.primeFlipWeight p) f))) = ⊤ := by
  refine (negIndex_lap_lap_zeta_eq_top_or_flip hp hf hM hsupp ha hb hab).resolve_left ?_
  have ha1 : a ≠ 1 := fun h1 => by simp [h1, scale] at ha
  have hb1 : b ≠ 1 := fun h1 => by simp [h1, scale] at hb
  rw [negIndex_lap_lap_zetaKernel ha1 hb1, negIndex_zetaKernel]
  exact hR.encard_lt_top.ne

/-! ### Flip sets of every density -/

/-- An integer `n ≠ m` lies at logarithmic distance at least `log(1 + 1/m)` from `m`. -/
theorem log_one_add_inv_le_abs_log_sub {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : n ≠ m) :
    Real.log (1 + 1 / m) ≤ |Real.log n - Real.log m| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hnm : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))),
      ← Real.log_div hm0.ne' hn0.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hn0]
    have hq : (n : ℝ) / m ≤ 1 := (div_le_one hm0).mpr (by linarith)
    calc (1 + 1 / (m : ℝ)) * n = n + n / m := by ring
      _ ≤ m := by linarith
  · have hnm : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by linarith))),
      ← Real.log_div hn0.ne' hm0.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hm0, add_mul, one_mul, one_div, inv_mul_cancel₀ hm0.ne']
    exact hnm

/-- **Two weight kernels differ by one atom on a narrow window.** If `n₀` is the only `n ≥ 2`
whose lags `log n ± s` are shorter than `2a`, the kernels at a point of log-scale `s` differ by the
`n₀`-atom of the weight difference. -/
theorem weightKernel_sub_of_window (lam mu : ℕ → ℝ) {f : ℝ → ℝ} {a : ℝ}
    (ha : ∀ u, a ≤ |u| → f u = 0) (u : HeckeLattice) (n₀ : ℕ)
    (hwin : ∀ n : ℕ, 2 ≤ n → n ≠ n₀ → 2 * a ≤ |Real.log n + scale heckeLogScale u| ∧
      2 * a ≤ |-Real.log n + scale heckeLogScale u|) :
    weightKernel lam f u - weightKernel mu f u =
      (((if 2 ≤ n₀ then (mu n₀ - lam n₀) / Real.sqrt n₀ else 0) *
        (RHTower.crossCorr f f (Real.log n₀ + scale heckeLogScale u) +
          RHTower.crossCorr f f (-Real.log n₀ + scale heckeLogScale u)) : ℝ) : ℂ) := by
  set s := scale heckeLogScale u
  set k := EF.weilTest (cx f) (ArithmeticCastelnuovoSeveri.translate s (cx f))
  have hk : ∀ x, k x = (RHTower.crossCorr f f (x + s) : ℂ) := fun x =>
    weilTest_shift_eq_crossCorr f s x
  have hts : ∀ w : ℕ → ℝ, (∑' n : ℕ, ((if 2 ≤ n then w n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) =
      ((if 2 ≤ n₀ then w n₀ / Real.sqrt n₀ else 0 : ℝ) : ℂ) *
        (k (Real.log n₀) + k (-Real.log n₀)) := by
    intro w
    refine tsum_eq_single n₀ fun n hn => ?_
    by_cases h2 : 2 ≤ n
    · obtain ⟨h1, h1'⟩ := hwin n h2 hn
      rw [hk, hk, crossCorr_eq_zero_of_support ha h1, crossCorr_eq_zero_of_support ha h1']
      simp
    · simp [h2]
  show RHTower.weilFullFunctional lam k - RHTower.weilFullFunctional mu k = _
  unfold RHTower.weilFullFunctional
  rw [hts, hts, hk, hk]
  split_ifs <;> push_cast <;> ring

/-- The twin of `ζ` that flips the sign of `Λ` at the odd powers of every prime in `P`. -/
def primeSetFlipWeight (P : Set ℕ) (n : ℕ) : ℝ :=
  ArithmeticCountingPositivity.primeSetFlip P n * ArithmeticFunction.vonMangoldt n

theorem primeSetFlip_sq (P : Set ℕ) {p : ℕ} (hp : p.Prime) :
    ArithmeticCountingPositivity.primeSetFlip P (p ^ 2) = 1 := by
  rw [ArithmeticCountingPositivity.primeSetFlip_eq_finiteFlip_of_le P le_rfl,
    RenormalizedArithmeticPotentialTheory.finiteFlip_prime_pow hp]
  split_ifs <;> norm_num

open Classical in
/-- **The coupling of a tower reads the flip set.** For every set of primes `P`, of any density,
every prime `p` and every real test supported in `[−a, a]` with `2a ≤ log(1 + 1/p²)`, the
`(p, p)`-coupling of the `P`-flip twin differs from that of `ζ` by `−4 log p ‖f‖²/√p` when
`p ∈ P` and not at all when `p ∉ P`. -/
theorem coupling_primeSetFlip_sub_coupling_zeta (P : Set ℕ) {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    {a : ℝ} (ha : ∀ u, a ≤ |u| → f u = 0) (hap : 2 * a ≤ Real.log (1 + 1 / (p : ℝ) ^ 2)) :
    coupling (weightKernel (primeSetFlipWeight P) f) (primeElt hp) (primeElt hp) -
      coupling (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
        (primeElt hp) (primeElt hp) =
      ((if p ∈ P then -(4 * Real.log p * RHTower.crossCorr f f 0 / Real.sqrt p) else 0 : ℝ) : ℂ) := by
  set Λ' : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ hp1
  have hlogp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the window is narrower than the gaps between integers near `p` and `p²`
  have hw1 : Real.log (1 + 1 / (p : ℝ) ^ 2) ≤ Real.log (1 + 1 / p) :=
    Real.log_le_log (by positivity) (by
      have : 1 / (p : ℝ) ^ 2 ≤ 1 / p :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith)
  have hw2 : Real.log (1 + 1 / (p : ℝ) ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by
      have : 1 / (p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hpp
      linarith)
  have hlogn : ∀ n : ℕ, 2 ≤ n → Real.log 2 ≤ Real.log n := fun n hn =>
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hs1 : scale heckeLogScale (primeElt hp) = Real.log p := scale_primeElt hp
  have hs2 : scale heckeLogScale (primeElt hp * primeElt hp) = 2 * Real.log p := by
    rw [scale_mul, hs1]; ring
  have hs0 : scale heckeLogScale (1 : HeckeLattice) = 0 := by simp [scale]
  -- the three tower points
  have d0 := weightKernel_sub_of_window (primeSetFlipWeight P) Λ' ha 1 0 fun n hn _ => by
    rw [hs0, add_zero, add_zero, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))]
    exact ⟨by linarith [hlogn n hn], by linarith [hlogn n hn]⟩
  have d1 := weightKernel_sub_of_window (primeSetFlipWeight P) Λ' ha (primeElt hp) p fun n hn hnp => by
    rw [hs1]
    have hgap := log_one_add_inv_le_abs_log_sub (m := p) hp.one_lt.le (by omega) hnp
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (by linarith [hlogn n hn])]; linarith [hlogn n hn]
    · rw [show -Real.log n + Real.log p = -(Real.log n - Real.log p) by ring, abs_neg]; linarith
  have d2 := weightKernel_sub_of_window (primeSetFlipWeight P) Λ' ha (primeElt hp * primeElt hp)
      (p ^ 2) fun n hn hnp => by
    rw [hs2]
    have hgap := log_one_add_inv_le_abs_log_sub (m := p ^ 2) (Nat.one_le_pow _ _ hp.pos)
      (by omega) hnp
    have hlp2 : Real.log ((p : ℝ) ^ 2) = 2 * Real.log p := by rw [Real.log_pow]; push_cast; ring
    push_cast at hgap
    rw [hlp2] at hgap
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (by linarith [hlogn n hn])]; linarith [hlogn n hn]
    · rw [show -Real.log n + 2 * Real.log p = -(Real.log n - 2 * Real.log p) by ring, abs_neg]; linarith
  -- evaluate the atoms
  have hcc2 : RHTower.crossCorr f f (Real.log p + Real.log p) = 0 :=
    crossCorr_eq_zero_of_support ha (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hΛp : Λ' p = Real.log p := ArithmeticFunction.vonMangoldt_apply_prime hp
  have hΛp2 : primeSetFlipWeight P (p ^ 2) = Λ' (p ^ 2) := by
    rw [primeSetFlipWeight, primeSetFlip_sq P hp, one_mul]
  rw [if_neg (by norm_num : ¬ 2 ≤ 0), zero_mul, Complex.ofReal_zero] at d0
  rw [if_pos (Nat.Prime.two_le hp), hs1, hcc2, neg_add_cancel, zero_add] at d1
  rw [if_pos (hp.two_le.trans (Nat.le_self_pow two_ne_zero p)), hΛp2, sub_self, zero_div,
    zero_mul, Complex.ofReal_zero] at d2
  simp only [coupling]
  by_cases hpP : p ∈ P
  · have hfl : primeSetFlipWeight P p = -Real.log p := by
      rw [primeSetFlipWeight, RenormalizedIntersectionTheory.primeSetFlip_prime_of_mem P hp hpP,
        ArithmeticFunction.vonMangoldt_apply_prime hp]; ring
    rw [hΛp, hfl] at d1
    rw [if_pos hpP]
    push_cast at d1 ⊢
    linear_combination d2 - 2 * d1 + d0
  · have hfl : primeSetFlipWeight P p = Real.log p := by
      rw [primeSetFlipWeight, RenormalizedIntersectionTheory.primeSetFlip_prime_of_notMem P hp hpP,
        ArithmeticFunction.vonMangoldt_apply_prime hp]; ring
    rw [hΛp, hfl, sub_self, zero_div, zero_mul, Complex.ofReal_zero] at d1
    rw [if_neg hpP, Complex.ofReal_zero]
    linear_combination d2 - 2 * d1 + d0

open Classical in
/-- **The coupling recovers the flip set.** For a nonzero test with `2a ≤ log(1 + 1/p²)`, the prime
`p` is flipped iff the `(p, p)`-coupling of the twin differs from that of `ζ`. -/
theorem mem_iff_coupling_primeSetFlip_ne (P : Set ℕ) {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hM : 0 < ∫ u, f u ^ 2) {a : ℝ} (ha : ∀ u, a ≤ |u| → f u = 0)
    (hap : 2 * a ≤ Real.log (1 + 1 / (p : ℝ) ^ 2)) :
    p ∈ P ↔ coupling (weightKernel (primeSetFlipWeight P) f) (primeElt hp) (primeElt hp) ≠
      coupling (weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
        (primeElt hp) (primeElt hp) := by
  rw [← sub_ne_zero, coupling_primeSetFlip_sub_coupling_zeta P hp ha hap]
  have hcc : RHTower.crossCorr f f 0 = ∫ u, f u ^ 2 := by
    simp only [RHTower.crossCorr, sub_zero, sq]
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  constructor
  · intro hpP
    rw [if_pos hpP, hcc]
    exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr
      (div_pos (mul_pos (mul_pos four_pos hlp) hM) hsq).ne')
  · intro hne
    by_contra hpP
    rw [if_neg hpP, Complex.ofReal_zero] at hne
    exact hne rfl

end GaloisForLFunctions.ArithmeticCouplingTheory
