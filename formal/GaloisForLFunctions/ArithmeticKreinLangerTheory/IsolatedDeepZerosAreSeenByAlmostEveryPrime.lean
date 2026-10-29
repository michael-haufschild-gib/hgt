import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.GrowthReadsTheDepthOfTheDeepestPair

/-!
# Isolated deep zeros are seen by almost every prime

The tower Hasse principle (`TowerFaithfulSpectraAreDecidedByAlmostEveryTower`) covers finitely many
pairs; fine towers (`FineTowersDecideEveryOrbitKernel`) cover every orbit kernel. For the coarse prime
towers and a single test, with infinitely many zeros, positivity on a tower must defeat the growth of
the deepest nodes against an infinite remainder. This module proves that it never can when the
deepest zeros are **isolated in depth**.

**Isolated depth.** A finite nonempty set `T` of zeros at depth `½ − Re ρ = D > 0`, every other zero
at depth `≤ D' < D`, and nonzero weights on `T`.

**Growth along one tower** (`not_bounded_orbitKernel_pow`, `not_isPosDefKernel_orbitKernel_zpowers`).
Along `u^n`, `scale u > 0`, the orbit kernel is the finite top sum `Σ_{ρ∈T} W_ρ ν_ρ^n`, with
`|ν_ρ| = e^{D·scale u}`, plus a remainder bounded by `e^{max(D',0)·n·scale u} Σ|W_ρ|`. If the top
nodes are distinct, non-cancellation at the top modulus (`coeff_eq_zero_of_norm_le`) makes the kernel
unbounded along the tower, so it is not positive definite there.

**Almost every prime** (`finite_primes_posDef_of_isolated_depth`). Two zeros alias at most at one
prime (`eq_of_alias_of_alias`), so all but finitely many prime towers separate the top nodes and see
a negative square, whatever the rest of the spectrum. For `ζ` with the cubic spline
(`zeta_finite_primes_posDef_of_isolated_depth`): if the off-line zeros have finitely many deepest
members isolated in depth, positivity of the Weil kernel fails on all but finitely many prime
towers. What remains open is depth accumulation, where the deepest zeros are not attained or not
isolated.
-/

open Complex Finset Filter
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests cx_contDiff cx_hasCompactSupport
  summable_norm_Wsummand rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (Sees sees_reflect seenRightZeros
  seenRightZeros_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

theorem logChar_neg_apply {G : Type*} [Group G] (ℓ : G →* Multiplicative ℝ) (s : ℂ) (u : G) :
    logChar ℓ (-s) u = (logChar ℓ s u)⁻¹ := by
  rw [logChar_apply, logChar_apply, neg_mul, Complex.exp_neg]

section IsolatedDepth

variable {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ} (hf : f ∈ realTests)
  {T : Finset ℂ} (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier) (hTne : T.Nonempty) {D D' : ℝ}
  (hDD : max D' 0 < D) (htop : ∀ ρ ∈ T, 1 / 2 - ρ.re = D)
  (hgap : ∀ ρ ∈ Z.carrier, ρ ∉ T → 1 / 2 - ρ.re ≤ D')
  (hW : ∀ ρ ∈ T, Z.Wsummand (cx f) (cx f) ρ ≠ 0)
include hZ hf hT hTne hDD htop hgap hW

/-- **Growth along one tower.** If the top nodes are distinct along `⟨u⟩`, `scale u > 0`, the
orbit kernel is unbounded along `u^n`. -/
theorem not_bounded_orbitKernel_pow {u : HeckeLattice} (hu : 0 < scale heckeLogScale u)
    (hinj : Set.InjOn (fun ρ => logChar heckeLogScale (1 / 2 - ρ) u) T) :
    ¬ ∃ B : ℝ, ∀ n : ℕ, ‖orbitKernel Z f (u ^ n)‖ ≤ B := by
  classical
  rintro ⟨B, hB⟩
  set s := scale heckeLogScale u with hs
  set W : ℂ → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ with hWdef
  set ν : ℂ → ℂ := fun ρ => logChar heckeLogScale (1 / 2 - ρ) u with hνdef
  set R := Real.exp (D * s)
  set r := Real.exp (max D' 0 * s)
  have hr1 : 1 ≤ r := Real.one_le_exp (mul_nonneg (le_max_right _ _) hu.le)
  have hrR : r < R := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hDD hu)
  have hnorm : ∀ ρ, ‖ν ρ‖ = Real.exp ((1 / 2 - ρ.re) * s) := fun ρ => by
    simp only [hνdef, norm_logChar, sub_re, one_div, inv_re, normSq_ofNat]
    norm_num [hs]
  have hνT : ∀ ρ ∈ T, ‖ν ρ‖ = R := fun ρ hρ => by rw [hnorm, htop ρ hρ]
  have hνrest : ∀ ρ ∈ Z.carrier, ρ ∉ T → ‖ν ρ‖ ≤ r := fun ρ hρ hρT => by
    rw [hnorm]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((hgap ρ hρ hρT).trans (le_max_left _ _)) hu.le)
  have hsumW := summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  set S := ∑' ρ : Z.carrier, ‖W ρ‖
  -- the kernel along the tower: top sum plus remainder
  have hterm : ∀ (n : ℕ) (ρ : ℂ), orbitTerm Z f (u ^ n) ρ = W ρ * ν ρ ^ n := fun n ρ => by
    simp only [orbitTerm, map_pow, hWdef, hνdef]; ring
  set E : ℕ → ℂ := fun n => ∑' ρ : Z.carrier, if (ρ : ℂ) ∈ T then 0 else W ρ * ν ρ ^ n
  have hsplit : ∀ n : ℕ, orbitKernel Z f (u ^ n) = ∑ ρ ∈ T, W ρ * ν ρ ^ n + E n := fun n => by
    have hsum := summable_orbitTerm hZ hf (u ^ n)
    have htopsum : ∑' ρ : Z.carrier, (if (ρ : ℂ) ∈ T then W ρ * ν ρ ^ n else 0) =
        ∑ ρ ∈ T, W ρ * ν ρ ^ n := by
      rw [tsum_eq_sum (s := T.subtype (· ∈ Z.carrier)) fun ρ hρ => if_neg fun h =>
        hρ (mem_subtype.mpr h)]
      rw [Finset.sum_subtype_of_mem (f := fun ρ => W ρ * ν ρ ^ n) hT |>.symm]
      exact sum_congr rfl fun ρ hρ => if_pos (mem_subtype.mp hρ)
    have hsT : Summable fun ρ : Z.carrier => if (ρ : ℂ) ∈ T then W ρ * ν ρ ^ n else 0 :=
      summable_of_ne_finset_zero (s := T.subtype (· ∈ Z.carrier)) fun ρ hρ =>
        if_neg fun h => hρ (mem_subtype.mpr h)
    have hsE : Summable fun ρ : Z.carrier => if (ρ : ℂ) ∈ T then 0 else W ρ * ν ρ ^ n := by
      refine (hsum.sub hsT).congr fun ρ => ?_
      rw [hterm]; split_ifs <;> ring
    rw [orbitKernel_eq_tsum, ← htopsum, ← hsT.tsum_add hsE]
    exact tsum_congr fun ρ => by rw [hterm]; split_ifs <;> ring
  -- the remainder grows at most like `r^n`
  have hE : ∀ n : ℕ, ‖E n‖ ≤ S * r ^ n := fun n => by
    have hb : ∀ ρ : Z.carrier, ‖(if (ρ : ℂ) ∈ T then 0 else W ρ * ν ρ ^ n)‖ ≤ ‖W ρ‖ * r ^ n :=
      fun ρ => by
        split_ifs with hρT
        · simp only [norm_zero]; positivity
        · rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
            (hνrest ρ ρ.2 hρT) n) (norm_nonneg _)
    calc ‖E n‖ ≤ ∑' ρ : Z.carrier, ‖W ρ‖ * r ^ n :=
          tsum_of_norm_bounded (hsumW.mul_right (r ^ n)).hasSum hb
      _ = S * r ^ n := tsum_mul_right
  -- non-cancellation at the top modulus
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨ρ₀, hρ₀⟩ := hTne
  have hz := coeff_eq_zero_of_norm_le (ι := T) (ν := fun ρ => ν ρ)
    (fun a b hab => Subtype.ext (hinj a.2 b.2 hab)) (fun ρ => W ρ) (zero_lt_one.trans_le hr1)
    (M := B + S) (fun n => by
      rw [Finset.sum_coe_sort T (fun ρ => W ρ * ν ρ ^ n)]
      have h1 : ∑ ρ ∈ T, W ρ * ν ρ ^ n = orbitKernel Z f (u ^ n) - E n := by rw [hsplit]; ring
      rw [h1]
      calc ‖orbitKernel Z f (u ^ n) - E n‖ ≤ B + S * r ^ n :=
            (norm_sub_le _ _).trans (add_le_add (hB n) (hE n))
        _ ≤ (B + S) * r ^ n := by nlinarith [one_le_pow₀ hr1 (n := n)])
    (i := ⟨ρ₀, hρ₀⟩) (by rw [hνT ρ₀ hρ₀]; exact hrR)
  exact hW ρ₀ hρ₀ hz

/-- **A tower separating the top nodes sees a negative square.** -/
theorem not_isPosDefKernel_orbitKernel_zpowers {u : HeckeLattice}
    (hu : 0 < scale heckeLogScale u)
    (hinj : Set.InjOn (fun ρ => logChar heckeLogScale (1 / 2 - ρ) u) T) :
    ¬ IsPosDefKernel (orbitKernel Z f ∘ zpowersHom _ u) := fun hpd =>
  not_bounded_orbitKernel_pow hZ hf hT hTne hDD htop hgap hW hu hinj
    ⟨((orbitKernel Z f ∘ zpowersHom _ u) 1).re, fun n => by
      have := hpd.norm_le (Multiplicative.ofAdd (n : ℤ))
      simpa [zpowersHom_apply] using this⟩

/-- **Almost every prime tower sees isolated deep zeros.** -/
theorem finite_primes_posDef_of_isolated_depth :
    {p : Nat.Primes | IsPosDefKernel (orbitKernel Z f ∘ zpowersHom _ (primeElt p.2))}.Finite := by
  classical
  -- the primes at which two top zeros alias
  set S : (ℂ × ℂ) → Set Nat.Primes := fun x =>
    {p | zeroChar x.1 (primeElt p.2) = zeroChar x.2 (primeElt p.2)}
  have hS : ∀ x ∈ (T ×ˢ T).filter (fun x => x.1 ≠ x.2), (S x).Finite := fun x hx =>
    Set.Subsingleton.finite fun p hp q hq =>
      Subtype.ext (eq_of_alias_of_alias (mem_filter.mp hx).2 p.2 q.2 hp hq)
  refine (Set.Finite.biUnion (s := ((T ×ˢ T).filter fun x => x.1 ≠ x.2 : Set (ℂ × ℂ))) (Finset.finite_toSet _)
    hS).subset fun p hp => ?_
  by_contra hnot
  refine not_isPosDefKernel_orbitKernel_zpowers hZ hf hT hTne hDD htop hgap hW
    (by rw [scale_primeElt]; exact Real.log_pos (by exact_mod_cast p.2.one_lt)) (fun ρ hρ ρ' hρ' h => ?_) hp
  by_contra hne
  apply hnot
  refine Set.mem_biUnion (x := (ρ, ρ'))
    (Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨hρ, hρ'⟩, hne⟩)) ?_
  show zeroChar ρ (primeElt p.2) = zeroChar ρ' (primeElt p.2)
  have h' : (logChar heckeLogScale (ρ - 1 / 2) (primeElt p.2))⁻¹ =
      (logChar heckeLogScale (ρ' - 1 / 2) (primeElt p.2))⁻¹ := by
    rw [← logChar_neg_apply, ← logChar_neg_apply, neg_sub, neg_sub]; exact h
  exact inv_injective h'

end IsolatedDepth

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

/-- **For `ζ`: isolated deepest off-line zeros fail positivity on almost every prime tower.** If
finitely many zeros left of the line sit at the largest depth `D > 0`, and all other zeros have depth
at most `D' < D`, then the Weil kernel is positive definite on only finitely many prime towers. -/
theorem zeta_finite_primes_posDef_of_isolated_depth {T : Finset ℂ}
    (hT : ∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier) (hTne : T.Nonempty) {D D' : ℝ}
    (hDD : max D' 0 < D) (htop : ∀ ρ ∈ T, 1 / 2 - ρ.re = D)
    (hgap : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ T → 1 / 2 - ρ.re ≤ D') :
    {p : Nat.Primes | IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt p.2))}.Finite :=
  finite_primes_posDef_of_isolated_depth temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hT
    hTne hDD htop hgap fun ρ hρ => zeta_Wsummand_ne_zero_of_left (hT ρ hρ)
      (by have := htop ρ hρ; have := le_max_right D' 0; linarith)

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms zeta_finite_primes_posDef_of_isolated_depth
