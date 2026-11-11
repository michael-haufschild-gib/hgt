import GaloisForLFunctions.FloorFreeArithmetic.EveryFiniteDatumIsATopLayer
import GaloisForLFunctions.FloorFreeArithmetic.FiniteLayersAreRealizedWithTheirMultiplicities
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# The zero configuration does not see the Euler product

Every receiver of the corpus consumes the zero configuration of `ζ`: ordinates, depths and
multiplicities. This module puts the Euler product into the floor calculus as a property of a
configuration and computes the floor of everything a configuration can carry at once.

`EulerDivisor Z`: the zeros of `Z` right of the critical line, with their multiplicities, are
the zero divisor on `Re s > ½` of a function `G` such that `G(s)/(s − 1)` is, on `Re s > 1`, an
Euler product over natural norms `q_k ≥ 2` and the Dirichlet series of its natural
coefficients, with linearly growing partial sums.

`EulerSymmetric`: temperedness (the explicit formula), the reflection symmetry (built into a
configuration), the conjugation symmetry, no real zeros, and `EulerDivisor`.

* `eulerSymmetric_zetaZeroConfig`: the zeros of `ζ` have the property, with the rational primes
  and `G(s) = (s − 1) ζ(s)`.
* `eulerSymmetric_layerConfig`: so has the configuration of every finite datum of depth
  `0 < b < ½`: positive ordinates with any multiplicities.
* `floor_eulerSymmetric`: the floor of the property is `½`, and it does not give the abscissa
  law (`not_forall_abscissaLaw_of_eulerSymmetric`).

A mechanism that acts on the zero configuration through these structures excludes nothing: for
such a mechanism the Euler product is not visible. A producer has to use the Euler product of
`ζ` on the function, not on its zeros.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa
open _root_.RHTower GaloisForLFunctions.RHTower

/-- The zeros of the configuration right of the critical line, with their multiplicities, are
the zero divisor there of `G`, where `G(s)/(s − 1)` is on `Re s > 1` an Euler product over
natural norms `q_k ≥ 2` and the Dirichlet series of its natural coefficients, whose partial
sums grow linearly. -/
def EulerDivisor (Z : ZeroConfig) : Prop :=
  ∃ (q : ℕ → ℕ) (G : ℂ → ℂ), (∀ k, 2 ≤ q k) ∧
    DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 < s.re →
      HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (G s / (s - 1)) ∧
      LSeriesHasSum (fun n => (genCoeff q n : ℂ)) s (G s / (s - 1))) ∧
    (∀ s : ℂ, 1 / 2 < s.re → (G s = 0 ↔ s ∈ Z.carrier)) ∧
    (∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → analyticOrderAt G ρ = Z.mult ρ) ∧
    ∃ A : ℝ, 0 < A ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (genCoeff q n : ℝ)) / N) atTop (𝓝 A)

/-- The mechanism of the structures a zero configuration can carry: the explicit formula, the
reflection and the conjugation symmetry, no real zeros, and the Euler product. -/
def EulerSymmetric : Mechanism := fun Z =>
  TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
    EulerDivisor Z

/-! ### The zeros of `ζ` -/

/-- The rational primes in increasing order. -/
def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

theorem two_le_nthPrime (k : ℕ) : 2 ≤ nthPrime k := (Nat.prime_nth_prime k).two_le

theorem log_nthPrime_mono (k : ℕ) :
    Real.log (nthPrime 0) ≤ Real.log (nthPrime k) :=
  Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le two_pos (two_le_nthPrime 0)))
    (by exact_mod_cast Nat.nth_monotone Nat.infinite_setOf_prime (Nat.zero_le k))

theorem summable_exp_log_nthPrime {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * Real.log (nthPrime k))) := by
  have hs : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ a)⁻¹ :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr ha)
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hs
  have hp : (0 : ℝ) < nthPrime k := by
    exact_mod_cast lt_of_lt_of_le two_pos (two_le_nthPrime k)
  have hle : (((k + 1 : ℕ) : ℝ)) ≤ nthPrime k := by
    exact_mod_cast (Nat.le_succ (k + 1)).trans (Nat.add_two_le_nth_prime k)
  rw [Real.exp_neg, mul_comm, ← Real.rpow_def_of_pos hp]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_le_rpow (by positivity) hle (by linarith))

/-- The Euler product of `ζ` over the primes in increasing order. -/
theorem hasProd_nthPrime {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * Real.log (nthPrime k))))⁻¹) (riemannZeta s) := by
  let e : ℕ ≃ Nat.Primes := Equiv.ofBijective
    (fun k => ⟨nthPrime k, Nat.prime_nth_prime k⟩)
    ⟨fun a b h => Nat.nth_injective Nat.infinite_setOf_prime (congrArg Subtype.val h),
      fun p => by
        have hp : (p : ℕ) ∈ Set.range (Nat.nth Nat.Prime) := by
          rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
          exact p.2
        obtain ⟨k, hk⟩ := hp
        exact ⟨k, Subtype.ext hk⟩⟩
  have hfun : (fun k => (1 - cexp (-(s * Real.log (nthPrime k))))⁻¹) =
      (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) ∘ e := by
    funext k
    have hne : ((nthPrime k : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le two_pos (two_le_nthPrime k)).ne'
    show (1 - cexp (-(s * Real.log (nthPrime k))))⁻¹ = (1 - ((nthPrime k : ℕ) : ℂ) ^ (-s))⁻¹
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log]
    congr 3
    ring
  rw [hfun]
  exact (Equiv.hasProd_iff e).mpr (riemannZeta_eulerProduct_hasProd hs)

theorem cexp_genEulerLog_nthPrime {s : ℂ} (hs : 1 < s.re) :
    cexp (genEulerLog nthPrime s) = zetaResidueUnit s / (s - 1) := by
  have hne : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have h := (hasProd_euler (log_gen_pos two_le_nthPrime) log_nthPrime_mono
    (fun a ha => summable_exp_log_nthPrime ha) hs).unique (hasProd_nthPrime hs)
  rw [zetaResidueUnit, Function.update_of_ne hne, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne)]
  exact h

/-- **The zeros of `ζ` right of the line are an Euler divisor**: of the rational primes, with
`G(s) = (s − 1) ζ(s)`. -/
theorem eulerDivisor_zetaZeroConfig : EulerDivisor zetaZeroConfig := by
  have hdiff : DifferentiableOn ℂ zetaResidueUnit {s : ℂ | 1 / 2 < s.re} := fun s _ =>
    (analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt
  have hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (nthPrime k))) :=
    fun a ha => summable_exp_log_nthPrime ha
  obtain ⟨A, hA, -, hcount⟩ := tendsto_genCoeff_count two_le_nthPrime log_nthPrime_mono hsum
    (σ₁ := 1 / 2) (by norm_num) hdiff (by rw [zetaResidueUnit_one]; exact one_ne_zero)
    (fun s hs => cexp_genEulerLog_nthPrime hs)
  have hmul : ∀ {s : ℂ}, s ≠ 1 → zetaResidueUnit s = (s - 1) * riemannZeta s := fun {s} hs => by
    rw [zetaResidueUnit, Function.update_of_ne hs]
  refine ⟨nthPrime, zetaResidueUnit, two_le_nthPrime, hdiff, fun s hs => ⟨?_, ?_⟩,
    fun s hs => ?_, fun ρ hρ hre => ?_, A, hA, hcount⟩
  · rw [← cexp_genEulerLog_nthPrime hs]
    exact hasProd_euler (log_gen_pos two_le_nthPrime) log_nthPrime_mono hsum hs
  · rw [← cexp_genEulerLog_nthPrime hs]
    exact hasSum_genCoeff two_le_nthPrime log_nthPrime_mono hsum hs
  · -- zeros of `(s − 1) ζ(s)` right of the line are the nontrivial zeros there
    rw [zetaZeroConfig_carrier, Set.mem_setOf_eq]
    by_cases h1 : s = 1
    · rw [h1, zetaResidueUnit_one]
      refine ⟨fun h => absurd h one_ne_zero, fun h => absurd h.2.2 ?_⟩
      rw [Complex.one_re]
      exact lt_irrefl _
    · rw [hmul h1, mul_eq_zero, or_iff_right (sub_ne_zero.mpr h1)]
      refine ⟨fun hz => ⟨hz, by linarith, ?_⟩, fun h => h.1⟩
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  · -- the order of `(s − 1) ζ(s)` at a zero is the order of `ζ`
    have hnt : IsNontrivialZero ρ := (Set.ext_iff.mp zetaZeroConfig_carrier ρ).mp hρ
    have hρ1 : ρ ≠ 1 := fun h => by
      have := hnt.2.2
      rw [h, Complex.one_re] at this
      exact lt_irrefl _ this
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hnt.2.1, hnt.2.2⟩]
      exact xi_orderAt_ne_top ρ
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := analyticAt_id.sub analyticAt_const
    have hzero : analyticOrderAt (fun s : ℂ => s - 1) ρ = 0 :=
      hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ1)
    have hcongr : analyticOrderAt zetaResidueUnit ρ =
        analyticOrderAt ((fun s : ℂ => s - 1) * riemannZeta) ρ :=
      analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hρ1)
    show analyticOrderAt zetaResidueUnit ρ = (((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℕ∞)
    rw [hcongr, analyticOrderAt_mul hsub (analyticOn_riemannZeta ρ hρ1), hzero, zero_add,
      ENat.coe_toNat hfin]

/-- **The zeros of `ζ` have all the structures of the mechanism.** -/
theorem eulerSymmetric_zetaZeroConfig : EulerSymmetric zetaZeroConfig :=
  ⟨temperedConfig_zetaZeroConfig, fun _ h => _root_.RHTower.conj_mem_zetaZeroConfig h,
    ArithmeticCastelnuovoSeveri.zetaZeroConfig_im_ne_zero', eulerDivisor_zetaZeroConfig⟩

/-! ### The configuration of a finite datum -/

/-- **The configuration of a finite datum is an Euler divisor**: its zeros right of the line,
`½ + b ± iγ` with the multiplicity of `γ`, are the zero divisor of the regular factor of an
Euler product over natural norms. -/
theorem eulerDivisor_layerConfig {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (Γ : Finset ℝ)
    (hΓ : ∀ γ ∈ Γ, 0 < γ) (m : ℝ → ℕ) (hm : ∀ γ, 1 ≤ m γ) :
    EulerDivisor (layerConfig hb'.le Γ m hm) := by
  classical
  obtain ⟨q, G, hq, hG, hprod, hzero, horder, hcount⟩ :=
    exists_integer_norm_euler_product_with_divisor (Θ := 1 / 2 + b) (by linarith) (by linarith)
      (γ := fun j : Γ => (j : ℝ)) Subtype.val_injective (fun j => hΓ j j.2) (fun j => m j)
  have hre_p : ∀ γ : ℝ, (((1 / 2 + b : ℝ) : ℂ) + γ * I).re = 1 / 2 + b := fun γ => by simp
  have him_p : ∀ γ : ℝ, (((1 / 2 + b : ℝ) : ℂ) + γ * I).im = γ := fun γ => by simp
  have hre_m : ∀ γ : ℝ, (((1 / 2 + b : ℝ) : ℂ) - γ * I).re = 1 / 2 + b := fun γ => by simp
  have him_m : ∀ γ : ℝ, (((1 / 2 + b : ℝ) : ℂ) - γ * I).im = -γ := fun γ => by simp
  -- a point of the carrier right of the line is `½ + b ± i|Im|`
  have hpoint : ∀ {ρ : ℂ} (him : |ρ.im| ∈ Γ), |ρ.re - 1 / 2| = b → 1 / 2 < ρ.re →
      ρ = ((1 / 2 + b : ℝ) : ℂ) + (((⟨|ρ.im|, him⟩ : Γ) : ℝ) : ℂ) * I ∨
        ρ = ((1 / 2 + b : ℝ) : ℂ) - (((⟨|ρ.im|, him⟩ : Γ) : ℝ) : ℂ) * I := by
    intro ρ him hre hgt
    have hsre : ρ.re = 1 / 2 + b := by
      rw [abs_of_pos (sub_pos.mpr hgt)] at hre
      linarith
    rcases le_or_gt 0 ρ.im with h0 | h0
    · left
      apply Complex.ext
      · rw [hre_p, hsre]
      · rw [him_p]
        exact (abs_of_nonneg h0).symm
    · right
      apply Complex.ext
      · rw [hre_m, hsre]
      · rw [him_m]
        show ρ.im = -|ρ.im|
        rw [abs_of_neg h0, neg_neg]
  refine ⟨q, G, hq, hG, hprod, fun s hs => ?_, fun ρ hρ hre => ?_, hcount⟩
  · rw [hzero s hs]
    constructor
    · rintro ⟨j, -, h | h⟩
      · rw [h]
        refine ⟨?_, ?_⟩
        · show |(((1 / 2 + b : ℝ) : ℂ) + ((j : ℝ) : ℂ) * I).re - 1 / 2| = b
          rw [hre_p, add_sub_cancel_left, abs_of_pos hb]
        · show |(((1 / 2 + b : ℝ) : ℂ) + ((j : ℝ) : ℂ) * I).im| ∈ Γ
          rw [him_p, abs_of_pos (hΓ j j.2)]
          exact j.2
      · rw [h]
        refine ⟨?_, ?_⟩
        · show |(((1 / 2 + b : ℝ) : ℂ) - ((j : ℝ) : ℂ) * I).re - 1 / 2| = b
          rw [hre_m, add_sub_cancel_left, abs_of_pos hb]
        · show |(((1 / 2 + b : ℝ) : ℂ) - ((j : ℝ) : ℂ) * I).im| ∈ Γ
          rw [him_m, abs_neg, abs_of_pos (hΓ j j.2)]
          exact j.2
    · rintro ⟨hre, him⟩
      exact ⟨⟨|s.im|, him⟩, Nat.one_le_iff_ne_zero.mp (hm _), hpoint him hre hs⟩
  · obtain ⟨hreρ, him⟩ := hρ
    have hj := horder ⟨|ρ.im|, him⟩
    show analyticOrderAt G ρ = ((m |ρ.im| : ℕ) : ℕ∞)
    rcases hpoint him hreρ hre with h | h
    · have h1 := hj.1
      rw [← h] at h1
      exact h1
    · have h2 := hj.2
      rw [← h] at h2
      exact h2

theorem eulerSymmetric_layerConfig {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (Γ : Finset ℝ)
    (hΓ : ∀ γ ∈ Γ, 0 < γ) (m : ℝ → ℕ) (hm : ∀ γ, 1 ≤ m γ) :
    EulerSymmetric (layerConfig hb'.le Γ m hm) :=
  ⟨temperedConfig_layerConfig hb'.le Γ m hm, conj_mem_layerConfig hb'.le Γ m hm,
    im_ne_zero_of_mem_layerConfig hb'.le Γ m hm hΓ, eulerDivisor_layerConfig hb hb' Γ hΓ m hm⟩

/-! ### The floor -/

private theorem one_pos_of_mem_singleton : ∀ γ ∈ ({1} : Finset ℝ), 0 < γ := fun γ hγ => by
  rw [Finset.mem_singleton.mp hγ]
  exact one_pos

/-- The mechanism has a model at every depth below `½`. -/
theorem hasModelAt_eulerSymmetric {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) :
    HasModelAt EulerSymmetric b :=
  ⟨_, eulerSymmetric_layerConfig hb hb' {1} one_pos_of_mem_singleton (fun _ => 1)
      (fun _ => le_rfl), _,
    mk_mem_layerConfig hb'.le {1} (fun _ => 1) (fun _ => le_rfl) hb one_pos_of_mem_singleton
      (Finset.mem_singleton_self 1), rfl⟩

/-- **The floor of everything a zero configuration can carry is `½`.** -/
theorem floor_eulerSymmetric : floor EulerSymmetric = 1 / 2 := by
  refine le_antisymm (floor_le_half _) ?_
  by_contra hlt
  have hlt' : floor EulerSymmetric < 1 / 2 := lt_of_not_ge hlt
  have h0 := floor_nonneg EulerSymmetric
  have hmodel := le_floor_of_hasModelAt (hasModelAt_eulerSymmetric
    (b := (floor EulerSymmetric + 1 / 2) / 2) (by linarith) (by linarith))
  linarith

/-- **The mechanism does not give the abscissa law.** -/
theorem not_forall_abscissaLaw_of_eulerSymmetric :
    ¬ ∀ Z, EulerSymmetric Z → AbscissaLaw Z := fun hall =>
  not_abscissaLaw_layerConfig (b := 1 / 4) (by norm_num) {1} (fun _ => 1) (fun _ => le_rfl)
    (by norm_num) one_pos_of_mem_singleton (Finset.singleton_nonempty 1)
    (hall _ (eulerSymmetric_layerConfig (b := 1 / 4) (by norm_num) (by norm_num) {1}
      one_pos_of_mem_singleton (fun _ => 1) (fun _ => le_rfl)))

end GaloisForLFunctions.FloorFreeArithmetic
