import GaloisForLFunctions.ZeroConfigurationGeometry.TheHeightCurvatureOfThePrimeChannel
import GaloisForLFunctions.ZeroConfigurationGeometry.TheSquaredGapIsReadAtSecondOrder
import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimesPinEveryFinitePieceOfZeta
import GaloisForLFunctions.ZeroConfigurationGeometry.RamanujanIsRealityOfAnEulerColumn
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SymmetricHalfCollisionLaw
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Near-Coincidence Prime Curvature and the Strip Collision Law

Near a height `T ∈ ℝ`, a functional-equation-symmetric pair of frequencies `T ± w` (`w² ∈ ℝ`) is
resolved at second order by the height curvature of the Weil test kernel: real pairs (`w = Δ ∈ ℝ`)
carry nonnegative squared gap `w² = Δ² ≥ 0`, whereas off-line pairs (`w = i δ`, `δ ≠ 0`) carry
strictly negative squared gap `w² = -δ² < 0`. Under the de Bruijn heat flow `H_t`, the dual dynamic
version of the same phenomenon asks when positive-time collisions of `H_t` can occur on the strip
scale `(0, (1/2) / log X]`.

1. **Exact second-moment explicit formula and second-order pair sign law**
   (`secondMomentKernel`, `neg_primeChannel_secondMomentKernel`,
   `zeta_secondMoment_explicit_primeCurvature`, `pair_secondOrder_sign_dichotomy`).
   For any windows `f, g` of aperture `r` and height `T ∈ ℝ`, the height-modulated second-moment
   kernel `s ↦ s² (f_T ⋆ g̃_T)(s)` evaluates `secondMoment (f ⋆ g̃) (γ_ρ - T)` across all nontrivial
   zeros `ρ` of `ζ`, with prime term identically equal to the height curvature
   `(d²/dT²) P_Λ(f_T ⋆ g̃_T)` — the finite `-(log n)²`-weighted prime-power sum over `n ≤ e^{2r}`.
   Around `T`, a real pair `T ± Δ` and an off-line pair `T ± i Δ` enter with opposite signs in
   front of `secondMoment (f ⋆ g̃) 0` up to `(5/48) Δ⁴ (2r)⁴ ∫ |f ⋆ g̃|`.

2. **Bounded-aperture Euler-column obstruction and strip collision obstruction below `(1/2)/log X`**
   (`bounded_aperture_primeCurvature_obstruction`, `strip_saddle_and_pairModel_collision_obstruction`).
   At every bounded aperture `r`, any weight agreeing with `Λ` on `primeRange r` has identical
   `(log n)²`-weighted prime curvature at all heights `T`, while an off-line Euler column at a prime
   `p > e^{2|r|}` has strictly negative squared gap `-δ² < 0` (`δ ∈ (0, 1/2]`) yet produces the
   exact same modulated zero-side pairing as an on-line lattice across all heights `T`. Dynamically,
   for `X > max (2π) e`, the Gaussian saddle `1/2 + t log(X / 2π)` stays outside the Euler-product
   half-plane `Re s > 1` throughout `(0, (1/2) / log(X / 2π)]` (containing `(0, (1/2) / log X]`),
   and the Lindelöf-bounded Riemann-density strip model `pairModel (log X) δ` undergoes an exact
   nondegenerate order-2 real collision strictly inside `(0, (1/2) / log X)`.

3. **Unconditional sub-Weyl pincer and global equivalence**
   (`offLine_squaredGap_and_subWeyl_pincer`,
   `nearCoincidence_and_stripCollision_global_equivalence`).
   Every off-line zero `ρ` of `ξ` (`Im ρ ≥ X₀`, `((i(Re ρ - 1/2))²).re < 0`) forces
   `c (Re ρ - 1/2)² / log(Im ρ) ≤ Λ_{Im ρ}`, while unconditionally
   `Λ_X ≤ (6600 / 9991 + ε) / log X` eventually. Globally across all heights, nonnegativity of the
   FE-pair squared gap of every zero of `ξ`, full-cone Weil positivity of `Λ`, vanishing of all
   `Λ_X`, absence of positive-time real collisions of `H_t`, absence of symmetric-half collisions on
   `(0, (6600 / 9991 + 1 / 20000) / log X]` (`X ≥ X₁`) plus the compact low-height box, and
   `RiemannHypothesis` are mutually equivalent.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.HTGeometry SelbergClass.PositiveFiniteEuler

/-! ### 1. Second-moment explicit formula via `(log n)²`-weighted primes -/

/-- Modulating a window to height `T` preserves `ApertureWindow r`. -/
theorem ApertureWindow.modulate (T : ℝ) {r : ℝ} {f : ℝ → ℂ} (hf : ApertureWindow r f) :
    ApertureWindow r (ZeroConfigurationGeometry.modulate T f) :=
  ⟨hf.1.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp),
    (tsupport_modulate_subset T f).trans hf.2⟩

/-- The cross-correlation `EF.weilTest f g` of two aperture-`r` windows has topological support in
`[-(2r), 2r]`. -/
theorem tsupport_weilTest_subset {r : ℝ} {f g : ℝ → ℂ} (hf : ApertureWindow r f)
    (hg : ApertureWindow r g) :
    tsupport (EF.weilTest f g) ⊆ Icc (-(2 * r)) (2 * r) :=
  closure_minimal
    (fun _ hs => abs_le.mp (not_lt.mp fun hlt => hs (weilTest_eq_zero_of_lt hf.2 hg.2 hlt)))
    isClosed_Icc

/-- The height-modulated second-moment kernel `s ↦ s² (f_T ⋆ g̃_T)(s)`. -/
def secondMomentKernel (f g : ℝ → ℂ) (T : ℝ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ 2 * EF.weilTest (modulate T f) (modulate T g) s

/-- Modulating the windows commutes with multiplying `EF.weilTest f g` by `s²`. -/
theorem secondMomentKernel_eq_modulate (f g : ℝ → ℂ) (T : ℝ) :
    secondMomentKernel f g T = modulate T (fun s : ℝ => (s : ℂ) ^ 2 * EF.weilTest f g s) := by
  funext s
  simp only [secondMomentKernel, modulate, weilTest_modulate]
  ring

/-- The Fourier transform of `secondMomentKernel f g T` at `w` is the height-shifted second moment
`secondMoment (EF.weilTest f g) (w - T)`. -/
theorem paperFT_secondMomentKernel (f g : ℝ → ℂ) (T : ℝ) (w : ℂ) :
    paperFT (secondMomentKernel f g T) w = secondMoment (EF.weilTest f g) (w - T) := by
  rw [secondMomentKernel_eq_modulate, paperFT_modulate, secondMoment]

/-- On aperture-`r` windows, minus the prime channel of `secondMomentKernel f g T` equals the
height curvature `(d²/dT²) P_λ(f_T ⋆ g̃_T)` — the finite `-(log n)²`-weighted prime-power sum up to
`e^{2r}`. -/
theorem neg_primeChannel_secondMomentKernel (lam : ℕ → ℝ) {r : ℝ} {f g : ℝ → ℂ}
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) (T : ℝ) :
    -primeChannel lam (secondMomentKernel f g T) =
      deriv (deriv fun x : ℝ => primeChannel lam (EF.weilTest (modulate x f) (modulate x g))) T := by
  have hmf := hf.modulate T
  have hmg := hg.modulate T
  have hsupp : ∀ s, 2 * r < |s| → secondMomentKernel f g T s = 0 := fun s hs => by
    simp only [secondMomentKernel, weilTest_eq_zero_of_lt hmf.2 hmg.2 hs, mul_zero]
  rw [primeChannel_eq_sum lam hsupp, deriv_deriv_primeChannel_modulate lam hf hg T]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [secondMomentKernel, weilTest_modulate]
  push_cast
  rw [show cexp (-(I * (T : ℂ) * Complex.log (n : ℂ))) =
        cexp (-(I * Complex.log (n : ℂ)) * (T : ℂ)) by congr 1; ring,
      show cexp (-(I * (T : ℂ) * -Complex.log (n : ℂ))) =
        cexp (I * Complex.log (n : ℂ) * (T : ℂ)) by congr 1; ring]
  ring

/-- **Exact second-moment explicit formula via `(log n)²`-weighted primes.** For any aperture-`r`
windows `f, g` and height `T ∈ ℝ`, the height-centred second-moment sum over all nontrivial zeros of
`ζ` converges absolutely and equals the sum of the pole second moments at `±i/2 - T`, the
`(log n)²`-weighted prime-channel height curvature `(d²/dT²) P_Λ(f_T ⋆ g̃_T)`, and the archimedean
second-moment integral. -/
theorem zeta_secondMoment_explicit_primeCurvature {r : ℝ} {f g : ℝ → ℂ}
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) (T : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℂ) * secondMoment (EF.weilTest f g) (gammaOf ρ - T)) ∧
      (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℂ) * secondMoment (EF.weilTest f g) (gammaOf ρ - T)) =
        secondMoment (EF.weilTest f g) (I / 2 - T) +
          secondMoment (EF.weilTest f g) (-I / 2 - T) +
          deriv (deriv fun x : ℝ =>
            primeChannel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (EF.weilTest (modulate x f) (modulate x g))) T +
          (1 / (2 * Real.pi) : ℂ) *
            ∫ u : ℝ, secondMoment (EF.weilTest f g) (u - T) * (EF.gammaBracket u : ℂ) := by
  have hmf := hf.modulate T
  have hmg := hg.modulate T
  have hkd : ContDiff ℝ 2 (EF.weilTest (modulate T f) (modulate T g)) :=
    EF.weilTest_contDiff hmf.1 hmg.1.continuous hmf.hasCompactSupport
  have hkc : HasCompactSupport (EF.weilTest (modulate T f) (modulate T g)) :=
    EF.weilTest_hasCompactSupport hmf.hasCompactSupport hmg.hasCompactSupport
  have hsd : ContDiff ℝ 2 (secondMomentKernel f g T) :=
    (Complex.ofRealCLM.contDiff.pow 2).mul hkd
  have hsc : HasCompactSupport (secondMomentKernel f g T) := hkc.mul_left
  obtain ⟨hsum, heq⟩ := WeilEF.EF_lit_zetaZeroConfig (secondMomentKernel f g T) hsd hsc
  rw [← _root_.RHTower.weilFullFunctional_vonMangoldt] at heq
  have hfun : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (secondMomentKernel f g T) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℂ) * secondMoment (EF.weilTest f g) (gammaOf ρ - T) := by
    funext ρ
    rw [paperFT_secondMomentKernel]
  rw [hfun] at hsum heq
  refine ⟨hsum, heq.trans ?_⟩
  change paperFT (secondMomentKernel f g T) (I / 2) +
      paperFT (secondMomentKernel f g T) (-I / 2) -
      primeChannel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (secondMomentKernel f g T) +
      (1 / (2 * Real.pi) : ℂ) *
        (∫ u : ℝ, paperFT (secondMomentKernel f g T) u * (EF.gammaBracket u : ℂ)) = _
  rw [sub_eq_add_neg _ (primeChannel _ _),
    neg_primeChannel_secondMomentKernel _ hf hg T,
    paperFT_secondMomentKernel, paperFT_secondMomentKernel]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [paperFT_secondMomentKernel]

/-- Shifting a pair signal at height `T` on the modulated kernel `f_T ⋆ g̃_T` reduces to the pair
signal around `0` on the base kernel `f ⋆ g̃`. -/
theorem pairSignal_weilTest_modulate (f g : ℝ → ℂ) (T : ℝ) (w : ℂ) :
    pairSignal (EF.weilTest (modulate T f) (modulate T g)) T w =
      pairSignal (EF.weilTest f g) 0 w := by
  have hmod : EF.weilTest (modulate T f) (modulate T g) = modulate T (EF.weilTest f g) := by
    funext s; rw [weilTest_modulate, modulate, mul_comm]
  simp only [pairSignal, hmod, paperFT_modulate]
  have h1 : (T : ℂ) + w - T = w := by ring
  have h2 : (T : ℂ) - w - T = -w := by ring
  have h3 : (T : ℂ) - T = 0 := sub_self _
  rw [h1, h2, h3, zero_add, zero_sub]

/-- **Second-order pair sign dichotomy around height `T`.** On modulated Weil kernels of aperture
`r`, a real pair `T ± Δ` has nonnegative squared gap `Δ² ≥ 0` and enters `pairSignal` with
`-Δ² · secondMoment (f ⋆ g̃) 0`, whereas an off-line FE pair `T ± i δ` has nonpositive squared gap
`-δ² ≤ 0` (`< 0` for `δ ≠ 0`) and enters with `+δ² · secondMoment (f ⋆ g̃) 0`. -/
theorem pair_secondOrder_sign_dichotomy {r : ℝ} {f g : ℝ → ℂ}
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) (T : ℝ) :
    let k := EF.weilTest f g
    let kT := EF.weilTest (modulate T f) (modulate T g)
    (∀ Δ : ℝ, |Δ| * (2 * r) ≤ 1 →
      0 ≤ (((Δ : ℂ) ^ 2).re) ∧
        ‖pairSignal kT T (Δ : ℂ) + ((Δ ^ 2 : ℝ) : ℂ) * secondMoment k 0‖ ≤
          5 / 48 * Δ ^ 4 * (2 * r) ^ 4 * ∫ s, ‖k s‖) ∧
    (∀ δ : ℝ, |δ| * (2 * r) ≤ 1 →
      (((I * (δ : ℂ)) ^ 2).re = -δ ^ 2) ∧
        ‖pairSignal kT T (I * (δ : ℂ)) - ((δ ^ 2 : ℝ) : ℂ) * secondMoment k 0‖ ≤
          5 / 48 * δ ^ 4 * (2 * r) ^ 4 * ∫ s, ‖k s‖) ∧
    (∀ Δ : ℝ, |Δ| * (2 * r) ≤ 1 →
      ‖pairSignal kT T (Δ : ℂ) - pairSignal kT T (I * (Δ : ℂ)) +
          2 * ((Δ ^ 2 : ℝ) : ℂ) * secondMoment k 0‖ ≤
        5 / 24 * Δ ^ 4 * (2 * r) ^ 4 * ∫ s, ‖k s‖) := by
  intro k kT
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf.1 hg.1.continuous hf.hasCompactSupport
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hf.hasCompactSupport hg.hasCompactSupport
  have hks : tsupport k ⊆ Icc (-(2 * r)) (2 * r) := tsupport_weilTest_subset hf hg
  refine ⟨fun Δ hΔ => ?_, fun δ hδ => ?_, fun Δ hΔ => ?_⟩
  · refine ⟨?_, ?_⟩
    · have hre : ((Δ : ℂ) ^ 2).re = Δ ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hre]; exact sq_nonneg Δ
    · have h := norm_pairSignal_add_sq_mul_secondMoment_le hkd.continuous hkc hks 0
        (w := (Δ : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hΔ)
      have hn : ‖(Δ : ℂ)‖ ^ 4 = Δ ^ 4 := by
        rw [Complex.norm_real, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs,
          ← pow_mul]
      rw [hn, ← Complex.ofReal_pow, Complex.ofReal_zero] at h
      dsimp only [kT, k]
      rw [pairSignal_weilTest_modulate]
      exact h
  · have hIsq : (I * (δ : ℂ)) ^ 2 = -((δ ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow]; ring
    refine ⟨?_, ?_⟩
    · rw [hIsq, Complex.neg_re, Complex.ofReal_re]
    · have h := norm_pairSignal_add_sq_mul_secondMoment_le hkd.continuous hkc hks 0
        (w := I * (δ : ℂ))
        (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hδ)
      have hn : ‖I * (δ : ℂ)‖ ^ 4 = δ ^ 4 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
      rw [hn, hIsq, neg_mul, ← sub_eq_add_neg, Complex.ofReal_zero] at h
      dsimp only [kT, k]
      rw [pairSignal_weilTest_modulate]
      exact h
  · have h := norm_realPair_sub_tiltedPair_le hkd.continuous hkc hks 0 Δ hΔ
    rw [← Complex.ofReal_pow, Complex.ofReal_zero] at h
    dsimp only [kT, k]
    rw [pairSignal_weilTest_modulate, pairSignal_weilTest_modulate]
    exact h

/-! ### 2. Bounded-aperture Euler-column obstruction and strip collision obstruction -/

/-- **Bounded-aperture prime-curvature and Euler-column obstruction.** At any bounded aperture `r`:
1. every arithmetic weight `lam` agreeing with `Λ` on `primeRange r` produces the identical
   `(log n)²`-weighted prime-channel height curvature across all heights `T` and all aperture-`r`
   windows;
2. there exists a prime `p` (`0 < log p`) such that for every off-line depth `δ ∈ (0, 1/2]`, every
   zero `s` of the Euler column `localFactor p (eulerColumnCoeff p δ)` has strictly negative
   off-line squared gap `((i (Re s - 1/2))²).re = -δ² < 0`, yet at every height `T` and on every
   aperture-`r` window `f`, the off-line column and the on-line lattice produce the exact same
   modulated zero-side pairing. -/
theorem bounded_aperture_primeCurvature_obstruction (r : ℝ) :
    (∀ lam : ℕ → ℝ,
      (∀ n ∈ primeRange r, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) →
      ∀ f g : ℝ → ℂ, ApertureWindow r f → ApertureWindow r g → ∀ T : ℝ,
        deriv (deriv fun x : ℝ => primeChannel lam (EF.weilTest (modulate x f) (modulate x g))) T =
          deriv (deriv fun x : ℝ =>
            primeChannel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (EF.weilTest (modulate x f) (modulate x g))) T) ∧
    (∃ p : ℕ, p.Prime ∧ ∃ hL : 0 < Real.log p,
      ∀ δ : ℝ, ∀ (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2),
        (∀ s ∈ (offLineLatticeConfig hL hδ hδ').carrier,
          ((I * ((depth s : ℝ) : ℂ)) ^ 2).re = -δ ^ 2 ∧ -δ ^ 2 < 0) ∧
        (∀ T : ℝ, ∀ f : ℝ → ℂ, ApertureWindow r f →
          (offLineLatticeConfig hL hδ hδ').W (modulate T f) (modulate T f) =
            (onLineLatticeConfig hL).W (modulate T f) (modulate T f))) := by
  refine ⟨fun lam hlam f g hf hg T => ?_, ?_⟩
  · rw [deriv_deriv_primeChannel_modulate lam hf hg T,
      deriv_deriv_primeChannel_modulate _ hf hg T]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    congr 2
    unfold primeWeight
    by_cases hn2 : 2 ≤ n
    · rw [if_pos hn2, if_pos hn2, hlam n hn hn2]
    · rw [if_neg hn2, if_neg hn2]
  · obtain ⟨p, hp, hL, hcol⟩ := no_bounded_aperture_excludes_eulerColumns r
    refine ⟨p, hp, hL, fun δ hδ hδ' => ?_⟩
    obtain ⟨hcar, hW⟩ := hcol δ hδ hδ'
    refine ⟨fun s hs => ?_, fun T f hf => hW (modulate T f) (hf.modulate T)⟩
    rw [hcar, mem_setOf_eq, localFactor_eulerColumnCoeff_eq_zero_iff hp.one_lt δ s] at hs
    have hd_sq : (depth s) ^ 2 = δ ^ 2 := by
      rcases hs with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp only [depth, verticalLatticePoint]; ring
      · simp only [depth, verticalLatticePoint]; ring
    have hre : ((I * ((depth s : ℝ) : ℂ)) ^ 2).re = -(depth s) ^ 2 := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, neg_one_mul, Complex.neg_re,
        Complex.ofReal_re]
    rw [hre, hd_sq]
    exact ⟨rfl, neg_lt_zero.mpr (sq_pos_of_pos hδ)⟩

/-- **Gaussian saddle barrier and strip collision obstruction across `(0, (1/2)/log X]`.** For every
height `X > max (2π) e`:
1. across the entire interval `t ∈ (0, (1/2) / log(X / 2π)]` — and in particular across all of
   `(0, (1/2) / log X]` — the Stirling–Gaussian saddle abscissa `1/2 + t log(X / 2π)` satisfies
   `1/2 + t log(X / 2π) ≤ 1`, never entering the Euler-product convergence half-plane `Re s > 1`;
2. strictly inside `(0, (1/2) / log X)`, there exist an off-line depth `δ ∈ (0, 1/2]` and a
   collision time `t_* ∈ (0, (1/2) / log X)` at which the Lindelöf-bounded Riemann-density strip
   source `pairModel (log X) δ` undergoes a nondegenerate order-2 real collision. -/
theorem strip_saddle_and_pairModel_collision_obstruction {X : ℝ}
    (hX : max (2 * Real.pi) (Real.exp 1) < X) :
    (∀ t : ℝ, 0 < t → t ≤ (1 / 2) / Real.log (X / (2 * Real.pi)) →
      1 / 2 + t * Real.log (X / (2 * Real.pi)) ≤ 1) ∧
    (∀ t : ℝ, 0 < t → t ≤ (1 / 2) / Real.log X →
      1 / 2 + t * Real.log (X / (2 * Real.pi)) < 1) ∧
    (∃ δ t_star : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < t_star ∧ t_star < (1 / 2) / Real.log X ∧
      (∀ x y : ℝ,
        ‖pairModel (Real.log X) δ (x + y * I)‖ ≤
          (x ^ 2 + y ^ 2 + δ ^ 2) * Real.cosh (Real.log X * y / 2)) ∧
      (∀ t : ℝ, 0 < t → t < t_star →
        ∃ y : ℝ, 0 < y ∧ pairModelHeat (Real.log X) δ t (y * I) = 0) ∧
      pairModelHeat (Real.log X) δ t_star 0 = 0 ∧
      deriv (pairModelHeat (Real.log X) δ t_star) 0 = 0 ∧
      deriv (deriv (pairModelHeat (Real.log X) δ t_star)) 0 ≠ 0) := by
  have hX2π : 2 * Real.pi < X := (le_max_left _ _).trans_lt hX
  have hXe : Real.exp 1 < X := (le_max_right _ _).trans_lt hX
  have h2π_gt1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hX_pos : 0 < X := h2π_pos.trans hX2π
  have hdiv_gt1 : 1 < X / (2 * Real.pi) := (one_lt_div h2π_pos).mpr hX2π
  have hL2π_pos : 0 < Real.log (X / (2 * Real.pi)) := Real.log_pos hdiv_gt1
  have hLX_pos : 0 < Real.log X :=
    zero_lt_one.trans (by simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hXe)
  have hdiv_lt : X / (2 * Real.pi) < X := div_lt_self hX_pos h2π_gt1
  have hlog_lt : Real.log (X / (2 * Real.pi)) < Real.log X :=
    Real.log_lt_log (by positivity) hdiv_lt
  refine ⟨fun t _ ht => ?_, fun t ht0 ht => ?_,
    exists_pairModelHeat_real_collision_below_scale hLX_pos (div_pos (by norm_num) hLX_pos)⟩
  · exact not_lt.mp ((gaussianSaddle_gt_one_iff hX2π).not.mpr (not_lt.mpr ht))
  · have ht_lt : t < (1 / 2) / Real.log (X / (2 * Real.pi)) :=
      ht.trans_lt (div_lt_div_of_pos_left (by norm_num) hL2π_pos hlog_lt)
    have hmul : t * Real.log (X / (2 * Real.pi)) < 1 / 2 :=
      (lt_div_iff₀ hL2π_pos).mp ht_lt
    linarith

/-! ### 3. Unconditional sub-Weyl pincer and global equivalence -/

/-- **Unconditional off-line squared-gap lower bound and sub-Weyl `6600/9991` pincer.** There exist
`c > 0` and `X₀ ≥ 4096` such that:
1. every zero `ρ` of `ξ` at height `Im ρ ≥ X₀` with negative FE-pair squared gap
   `((i (Re ρ - 1/2))²).re < 0` forces `0 < c (Re ρ - 1/2)² / log(Im ρ) ≤ Λ_{Im ρ}`;
2. for every `ε > 0`, `Λ_X ≤ (6600 / 9991 + ε) / log X` eventually as `X → ∞`;
3. at every height `X ≥ X₀` where `Λ_X = 0`, every zero `ρ` of `ξ` at height `Im ρ = X` lies on the
   critical line `Re ρ = 1/2` (`((i (Re ρ - 1/2))²).re = 0`). -/
theorem offLine_squaredGap_and_subWeyl_pincer :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      (∀ ρ : ℂ, xi ρ = 0 → X₀ ≤ ρ.im → ((I * ((depth ρ : ℝ) : ℂ)) ^ 2).re < 0 →
        0 < c * (depth ρ) ^ 2 / Real.log ρ.im ∧
          c * (depth ρ) ^ 2 / Real.log ρ.im ≤ localNewmanConstant ρ.im) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop,
        localNewmanConstant X ≤ (6600 / 9991 + ε) / Real.log X) ∧
      (∀ X : ℝ, X₀ ≤ X → localNewmanConstant X = 0 →
        ∀ ρ : ℂ, xi ρ = 0 → ρ.im = X → ρ.re = 1 / 2) := by
  obtain ⟨c, hc, X₀, hX₀, hlow⟩ := exists_le_localNewmanConstant_of_offLine_zero
  refine ⟨c, hc, X₀, hX₀, fun ρ hρ hX hneg => ?_, fun ε hε =>
    eventually_localNewmanConstant_le_subWeyl_logX hε, fun X hX hΛ ρ hρ him => ?_⟩
  · have hre : ((I * ((depth ρ : ℝ) : ℂ)) ^ 2).re = -(depth ρ) ^ 2 := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, neg_one_mul, Complex.neg_re,
        Complex.ofReal_re]
    rw [hre] at hneg
    have hd_pos : 0 < (depth ρ) ^ 2 := neg_lt_zero.mp hneg
    have hne : ρ.re ≠ 1 / 2 := fun heq => by
      simp [depth, heq] at hd_pos
    have hlog_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith)
    exact ⟨div_pos (mul_pos hc hd_pos) hlog_pos, hlow ρ hρ hX hne⟩
  · by_contra hne
    have hle := hlow ρ hρ (him ▸ hX) hne
    rw [him, hΛ] at hle
    have hd_pos : 0 < (ρ.re - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hlog_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith)
    have hpos : 0 < c * (ρ.re - 1 / 2) ^ 2 / Real.log X := by
      rw [← him]; exact div_pos (mul_pos hc hd_pos) hlog_pos
    linarith

/-- Nonnegativity of the FE-pair squared gap `((i (Re ρ - 1/2))²).re = -(Re ρ - 1/2)²` across all
zeros `ρ` of `ξ` is unconditionally equivalent to `RiemannHypothesis`. -/
theorem riemannHypothesis_iff_xi_fePair_squaredGap_nonneg :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → 0 ≤ ((I * ((depth ρ : ℝ) : ℂ)) ^ 2).re := by
  rw [riemannHypothesis_iff_riemannHeat_zero_real]
  constructor
  · intro hreal ρ hρ
    have hz : riemannHeat 0 (-I * (ρ - 1 / 2)) = 0 := by
      rw [riemannHeat_zero]
      have hid : (1 / 2 : ℂ) + I * (-I * (ρ - 1 / 2)) = ρ := by
        ring_nf; rw [Complex.I_sq]; ring
      rw [hid]; exact hρ
    have him := hreal _ hz
    have hdim : (-I * (ρ - 1 / 2)).im = -depth ρ := by
      simp [depth]
    have hd0 : depth ρ = 0 := by linarith
    simp [hd0]
  · intro hgap z hz
    rw [riemannHeat_zero] at hz
    have hnonneg := hgap (1 / 2 + I * z) hz
    have hd : depth (1 / 2 + I * z) = -z.im := by
      simp [depth]
    have hre : ((I * ((depth (1 / 2 + I * z) : ℝ) : ℂ)) ^ 2).re = -(z.im ^ 2) := by
      rw [hd, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, neg_sq, neg_one_mul,
        Complex.neg_re, Complex.ofReal_re]
    rw [hre] at hnonneg
    have hsq0 : z.im ^ 2 = 0 := le_antisymm (by linarith only [hnonneg]) (sq_nonneg z.im)
    exact sq_eq_zero_iff.mp hsq0

/-- **Global equivalence of FE-pair squared-gap reality, full-cone prime positivity, and sub-Weyl
strip collision exclusion.** Unconditionally, there exists `X₁ ≥ 30` such that the following are
mutually equivalent:
1. every zero `ρ` of `ξ` has nonnegative FE-pair squared gap `0 ≤ ((i (Re ρ - 1/2))²).re`;
2. `WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))`;
3. `∀ X : ℝ, localNewmanConstant X = 0`;
4. `∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0`;
5. absence of collisions on the compact low-height box `|x| ≤ X₁, t ∈ (0, 1/8]` together with
   absence of symmetric-half collisions of `halfGaussTransform t (xiLine X)` across the sub-Weyl
   strip window `t ∈ (0, (6600 / 9991 + 1 / 20000) / log X]` (`X ≥ X₁`), strictly smaller than both
   `(2/3) / log X` and the `1/2` saddle scale above `6600 / 9991 ≈ 0.6606`;
6. `RiemannHypothesis`. -/
theorem nearCoincidence_and_stripCollision_global_equivalence :
    ∃ X₁ : ℝ, 30 ≤ X₁ ∧
      (((∀ ρ : ℂ, xi ρ = 0 → 0 ≤ ((I * ((depth ρ : ℝ) : ℂ)) ^ 2).re) ↔ RiemannHypothesis) ∧
        (_root_.RHTower.WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ↔
          RiemannHypothesis) ∧
        ((∀ X : ℝ, localNewmanConstant X = 0) ↔ RiemannHypothesis) ∧
        ((∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ↔
          RiemannHypothesis) ∧
        (((∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
              riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
            (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((6600 / 9991 + 1 / 20000) / Real.log X),
              (halfGaussTransform t (xiLine X) 0).re = 0 →
                (deriv (halfGaussTransform t (xiLine X)) 0).im ≠ 0)) ↔
          RiemannHypothesis)) := by
  obtain ⟨X₁, hX₁30, h12, _, h14, h1RH⟩ :=
    question_2_6_5_global_equivalence (δ := 1 / 20000) (ε := 0) (by norm_num) (by norm_num)
      (by norm_num)
  exact ⟨X₁, hX₁30,
    riemannHypothesis_iff_xi_fePair_squaredGap_nonneg.symm,
    _root_.RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.symm,
    h1RH,
    h12.symm.trans h1RH,
    h14.symm.trans h1RH⟩

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_secondMoment_explicit_primeCurvature
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.pair_secondOrder_sign_dichotomy
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.bounded_aperture_primeCurvature_obstruction
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.strip_saddle_and_pairModel_collision_obstruction
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.offLine_squaredGap_and_subWeyl_pincer
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.nearCoincidence_and_stripCollision_global_equivalence

end GaloisForLFunctions.ZeroConfigurationGeometry
