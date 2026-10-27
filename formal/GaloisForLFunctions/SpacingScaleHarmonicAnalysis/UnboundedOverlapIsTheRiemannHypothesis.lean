import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# Unbounded overlap is the Riemann hypothesis

The atomic family of level `N` built from a bump `g` is spanned by the translates `g(· − log n)`,
`1 ≤ n ≤ N`. At a **fixed** width `w`, the overlap ratio `w/δ_N ≍ wN` grows without bound with `N`.
This file shows that positivity of Weil's form on all these families is exactly RH, for the cubic
spline `B = U_1^{⋆4}`, whose transform `(sin z/z)⁴` vanishes only on the real axis.

* **Translation invariance of Weil Grams** (`weilGram_translate_add`): shifting every translate by
  the same `c` leaves the Gram matrix unchanged.
* **The rational Hecke orbit lives in the atomic family** (`exists_add_mem_logShifts`): every finite
  set of shifts `log r`, `r ∈ ℚ_{>0}`, moves into `{log n : n ≥ 1}` after one common shift by the
  logarithm of a common denominator.
* **At every fixed width** (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`,
  `zeta_splineAtomic_negIndex_law_of_width`): the same holds for the spline `B_w = U_w^{⋆4}` of any
  width `w > 0`, however small; at fixed width the overlap ratio `wN` is unbounded in `N`.
* **Unbounded overlap is RH** (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero`): RH holds iff
  for every finite set of atoms `S ⊆ {log n : n ≥ 1}` the prime-side Weil Gram matrix of the
  translates `B(· − s)`, `s ∈ S`, is positive semidefinite; quantitatively, the largest negative
  index of these Gram matrices is the number of distinct zeros right of the critical line
  (`zeta_splineAtomic_negIndex_law`).

Together with the stability law at the spacing scale (`TheStabilityLawAtTheSpacingScale`) this
brackets the overlap ratio: at ratio `≤ c₀` positivity is unconditional, and on the atomic families
of one fixed bump — ratio `→ ∞` — it is the Riemann hypothesis. Only bounded overlap is left between
them.
-/

noncomputable section

open Zeta23

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open GaloisForLFunctions.HTGeometry (hermNegIndex hermNegIndex_submatrix_equiv)

/-- The atom positions `log n`, `n ≥ 1`. -/
def logShifts : Set ℝ := {v | ∃ n : ℕ, 1 ≤ n ∧ Real.log n = v}

theorem logShifts_subset_ratHeckeShifts : logShifts ⊆ ratHeckeShifts := by
  rintro v ⟨n, hn, rfl⟩
  exact ⟨n, by exact_mod_cast hn, by push_cast; rfl⟩

/-! ### Translation invariance -/

/-- **Translation invariance of Weil Grams**: a common shift of all translates leaves the Gram
matrix unchanged. -/
theorem weilGram_translate_add (lam : ℕ → ℝ) (g : ℝ → ℂ) (S : Finset ℝ) (c : ℝ) :
    weilGram lam (fun s : S => ArithmeticCastelnuovoSeveri.translate ((s : ℝ) + c) g) =
      weilGram lam (fun s : S => ArithmeticCastelnuovoSeveri.translate (s : ℝ) g) := by
  ext i j
  simp only [weilGram]
  congr 1
  funext u
  rw [weilTest_translate, weilTest_translate]
  congr 1
  ring

/-! ### The rational Hecke orbit inside the atomic family -/

/-- A positive rational is a ratio of positive integers. -/
theorem exists_nat_ratio_of_mem_ratHeckeShifts {s : ℝ} (hs : s ∈ ratHeckeShifts) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ s = Real.log p - Real.log q := by
  obtain ⟨r, hr, rfl⟩ := hs
  refine ⟨r.num.toNat, r.den, ?_, r.den_pos, ?_⟩
  · have := Rat.num_pos.mpr hr
    omega
  · have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      have h := Int.toNat_of_nonneg (Rat.num_pos.mpr hr).le
      exact_mod_cast h
    rw [hnum, ← Real.log_div (by exact_mod_cast (Rat.num_pos.mpr hr).ne')
      (by exact_mod_cast r.den_pos.ne')]
    congr 1
    rw [Rat.cast_def]

/-- **The rational Hecke orbit lives in the atomic family**: every finite set of rational Hecke
shifts moves into `{log n : n ≥ 1}` after one common shift. -/
theorem exists_add_mem_logShifts (S : Finset ℝ) (hS : ↑S ⊆ ratHeckeShifts) :
    ∃ c : ℝ, ∀ s ∈ S, s + c ∈ logShifts := by
  classical
  have hpq : ∀ s ∈ S, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ s = Real.log p - Real.log q :=
    fun s hs => exists_nat_ratio_of_mem_ratHeckeShifts (hS hs)
  choose! p q hp hq hpq using hpq
  set B : ℕ := ∏ s ∈ S, q s
  have hB : 0 < B := Finset.prod_pos fun s hs => hq s hs
  refine ⟨Real.log B, fun s hs => ?_⟩
  have hdvd : q s ∣ B := Finset.dvd_prod_of_mem q hs
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hk; omega
  refine ⟨p s * k, Nat.mul_pos (hp s hs) hk0, ?_⟩
  have key : s = Real.log (p s) - Real.log (q s) := hpq s hs
  have hp0 : (0 : ℝ) < p s := by exact_mod_cast hp s hs
  have hq0 : (0 : ℝ) < q s := by exact_mod_cast hq s hs
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hB' : ((B : ℕ) : ℝ) = (q s : ℝ) * k := by rw [hk]; push_cast; ring
  rw [hB', Nat.cast_mul, Real.log_mul hp0.ne' hk0'.ne', Real.log_mul hq0.ne' hk0'.ne']
  linarith

/-- The negative index of the Gram of translates over `S` equals that over `S + c`. -/
theorem negIndex_translate_add (lam : ℕ → ℝ) (g : ℝ → ℂ) (S : Finset ℝ) (c : ℝ) :
    hermNegIndex (weilGram lam fun s : S.image (· + c) =>
        ArithmeticCastelnuovoSeveri.translate (s : ℝ) g) =
      hermNegIndex (weilGram lam fun s : S => ArithmeticCastelnuovoSeveri.translate (s : ℝ) g) := by
  -- the reindexing `S ≃ S + c`
  have hinj : Function.Injective fun s : ℝ => s + c := add_left_injective c
  let e : S ≃ S.image (· + c) :=
    { toFun := fun s => ⟨(s : ℝ) + c, Finset.mem_image_of_mem _ s.2⟩
      invFun := fun t => ⟨(t : ℝ) - c, by
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp t.2
        rw [← hst, add_sub_cancel_right]; exact hs⟩
      left_inv := fun s => by ext; simp
      right_inv := fun t => by ext; simp }
  rw [← hermNegIndex_submatrix_equiv _ e, ← weilGram_translate_add lam g S c]
  rfl

/-! ### Unbounded overlap is RH -/

/-- **Unbounded overlap is RH**: RH holds iff the prime-side Weil Gram matrix of the translates of
the cubic spline by every finite set of atoms `log n` is positive semidefinite. -/
theorem riemannHypothesis_iff_splineAtomic_negIndex_eq_zero :
    RiemannHypothesis ↔ ∀ S : Finset ℝ, ↑S ⊆ logShifts → hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline)) = 0 := by
  rw [riemannHypothesis_iff_splineRatHecke_negIndex_eq_zero]
  constructor
  · exact fun h S hS => h S (hS.trans logShifts_subset_ratHeckeShifts)
  · intro h S hS
    obtain ⟨c, hc⟩ := exists_add_mem_logShifts S hS
    have hS' : ↑(S.image (· + c)) ⊆ logShifts := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      exact hc s hs
    rw [← negIndex_translate_add _ _ S c]
    exact h _ hS'

/-- **The atomic families of the spline count the right zeros**: some finite set of atoms carries a
Weil Gram with at least `n` negative squares iff `ζ` has at least `n` distinct zeros right of the
critical line. -/
theorem zeta_splineAtomic_negIndex_law (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ logShifts ∧ n ≤ hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline))) ↔
      (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  rw [← zeta_splineOrbit_negIndex_law denseShifts_ratHecke n]
  constructor
  · rintro ⟨S, hS, hn⟩
    exact ⟨S, hS.trans logShifts_subset_ratHeckeShifts, hn⟩
  · rintro ⟨S, hS, hn⟩
    obtain ⟨c, hc⟩ := exists_add_mem_logShifts S hS
    refine ⟨S.image (· + c), fun t ht => ?_, by rw [negIndex_translate_add]; exact hn⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hc s hs

/-! ### Every fixed width -/

open RHTower.WeilDeletion (upow paperFT_upow hasCompactSupport_upow)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (contDiff_upow paperFT_unif_ne_zero)

/-- The cubic spline of width `w`: `B_w = U_w^{⋆4}`, supported in `[−4w, 4w]`, `C²`. -/
theorem upow_mem_realTests {w : ℝ} (hw : 0 < w) : upow w 3 ∈ realTests :=
  ⟨by exact_mod_cast contDiff_upow hw 2, hasCompactSupport_upow w 3⟩

/-- `B_w` sees every zero right of the line: its transform `(sin(wz)/(wz))⁴` is real-rooted. -/
theorem seenRightZeros_upow (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) :
    seenRightZeros Z (upow w 3) = {ρ ∈ Z.carrier | 1 / 2 < ρ.re} := by
  have hne : ∀ z : ℂ, z.im ≠ 0 → paperFT (cx (upow w 3)) z ≠ 0 := fun z hz => by
    show paperFT (fun x => (upow w 3 x : ℂ)) z ≠ 0
    rw [paperFT_upow]
    exact pow_ne_zero _ (paperFT_unif_ne_zero hw hz)
  ext ρ
  simp only [seenRightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hre : ρ.re ≠ 1 / 2 := ne_of_gt h2
    refine ⟨h1, h2, hne _ (GaloisForLFunctions.SquareRootThreshold.im_gammaOf_ne_zero hre),
      hne _ ?_⟩
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr (GaloisForLFunctions.SquareRootThreshold.im_gammaOf_ne_zero hre)

/-- **At every fixed width the atomic families count the right zeros**: for `w > 0`, some finite set
of atoms carries a Weil Gram of translates of `B_w` with at least `n` negative squares iff `ζ` has at
least `n` distinct zeros right of the critical line. -/
theorem zeta_splineAtomic_negIndex_law_of_width {w : ℝ} (hw : 0 < w) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ logShifts ∧ n ≤ hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx (upow w 3)))) ↔
      (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  rw [← seenRightZeros_upow zetaZeroConfig hw,
    ← zeta_orientationIndex_law (upow_mem_realTests hw) denseShifts_ratHecke n]
  constructor
  · rintro ⟨S, hS, hn⟩
    exact ⟨S, hS.trans logShifts_subset_ratHeckeShifts, hn⟩
  · rintro ⟨S, hS, hn⟩
    obtain ⟨c, hc⟩ := exists_add_mem_logShifts S hS
    refine ⟨S.image (· + c), fun t ht => ?_, by rw [negIndex_translate_add]; exact hn⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hc s hs

/-- **At every fixed width, unbounded overlap is RH**: for every `w > 0`, RH holds iff every Weil
Gram of translates `B_w(· − log n)` over a finite set of atoms is positive semidefinite. -/
theorem riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width {w : ℝ} (hw : 0 < w) :
    RiemannHypothesis ↔ ∀ S : Finset ℝ, ↑S ⊆ logShifts → hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx (upow w 3))) = 0 := by
  rw [riemannHypothesis_iff_no_rightZero]
  constructor
  · intro h S hS
    by_contra hne
    obtain := (zeta_splineAtomic_negIndex_law_of_width hw 1).mp
      ⟨S, hS, Nat.one_le_iff_ne_zero.mpr hne⟩
    rw [h, Set.encard_empty] at *
    simp_all
  · intro h
    by_contra hne
    obtain ⟨S, hS, hn⟩ := (zeta_splineAtomic_negIndex_law_of_width hw 1).mpr
      (Set.one_le_encard_iff_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hne))
    rw [h S hS] at hn
    exact absurd hn (by norm_num)

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
