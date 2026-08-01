import GaloisForLFunctions.RHTower.MobiusMellinGammaNormalCone
import GaloisForLFunctions.RHTower.PrimeMobiusLoschmidtCofinalPurity
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Finite Möbius--Pluecker transfers and their cofinal normal-cone lift

This module realizes the exact finite source transfer, proves the fixed-aperture obstruction, and
constructs the nested cofinal finite-prime diagonal whose Euler-normal blow-up converges locally
uniformly to the reciprocal squarefree section on `re s > 1`.
-/

open Complex Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Euler half-plane on which every product in the diagonal construction converges absolutely. -/
def mobiusPlueckerEulerDomain : Set ℂ := {s | 1 < s.re}

/-- Prime Dirichlet monomial `p⁻ˢ`. -/
def primeDirichletTerm (p : Nat.Primes) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (-s)

theorem norm_primeDirichletTerm (p : Nat.Primes) (s : ℂ) :
    ‖primeDirichletTerm p s‖ = (p : ℝ) ^ (-s.re) := by
  rw [primeDirichletTerm, ← Complex.ofReal_natCast]
  exact Complex.norm_cpow_eq_rpow_re_of_pos
    (by exact_mod_cast p.2.pos) (-s)

theorem continuous_primeDirichletTerm (p : Nat.Primes) :
    Continuous (primeDirichletTerm p) := by
  haveI : NeZero (p : ℂ) :=
    ⟨by exact_mod_cast (Nat.Prime.ne_zero p.2)⟩
  change Continuous (fun s : ℂ => (p : ℂ) ^ (-s))
  exact (continuous_const_cpow (p : ℂ)).comp continuous_neg

theorem primeDirichletTerm_two_mul
    (p : Nat.Primes) (s : ℂ) :
    primeDirichletTerm p (2 * s) = primeDirichletTerm p s ^ 2 := by
  rw [primeDirichletTerm, primeDirichletTerm]
  rw [show -(2 * s) = (2 : ℂ) * (-s) by ring]
  simpa using Complex.cpow_nat_mul (p : ℂ) 2 (-s)

/-- Local finite reciprocal factor `(1-p⁻ˢigma)/(1+p⁻ˢ)`. -/
def mobiusPlueckerEulerFactor (sigma : ℝ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ((1 : ℂ) - primeDirichletTerm p (sigma : ℂ)) /
    ((1 : ℂ) + primeDirichletTerm p s)

/-- Finite reciprocal transfer over an actual finite prime aperture. -/
def finiteMobiusPlueckerTransfer
    (S : Finset Nat.Primes) (sigma : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, mobiusPlueckerEulerFactor sigma p s

/-- Safe finite squarefree correction from the paper construction. -/
def finiteMobiusPlueckerCorrection
    (S : Finset Nat.Primes) (sigma : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ S,
    ((1 : ℂ) - primeDirichletTerm p (2 * (sigma : ℂ))) /
      ((1 : ℂ) - primeDirichletTerm p (2 * s))

/-- Source-normalized signed Pluecker/Loschmidt amplitude. -/
def finiteMobiusPlueckerAmplitude
    (S : Finset Nat.Primes) (sigma : ℝ) (s : ℂ) : ℂ :=
  finitePrimeSignedSchurTransfer S sigma (s - sigma)

theorem primeDirichletTerm_eq_exp_neg_mul_log
    (p : Nat.Primes) (s : ℂ) :
    primeDirichletTerm p s =
      Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  rw [primeDirichletTerm,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast p.2.ne_zero)]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  congr 1
  ring

/-- The signed Schur source is exactly the finite Pluecker product from the paper. -/
theorem finiteMobiusPlueckerAmplitude_eq_prod
    (S : Finset Nat.Primes) (sigma : ℝ) (s : ℂ) :
    finiteMobiusPlueckerAmplitude S sigma s =
      ∏ p ∈ S,
        ((1 : ℂ) - primeDirichletTerm p s) /
          ((1 : ℂ) + primeDirichletTerm p (sigma : ℂ)) := by
  classical
  rw [finiteMobiusPlueckerAmplitude, finitePrimeSignedSchurTransfer]
  apply Finset.prod_congr rfl
  intro p hp
  rw [bernoulliSignedSchurFactor_prime_eq]
  have hweight :
      ((Real.exp (-sigma * Real.log (p : ℝ)) : ℝ) : ℂ) =
        primeDirichletTerm p (sigma : ℂ) := by
    change (primeSchurWeight sigma p : ℂ) =
      ((p : ℕ) : ℂ) ^ (-(sigma : ℂ))
    exact primeSchurWeight_eq_cpow sigma p
  rw [hweight]
  congr 2
  rw [show -((sigma : ℂ) + (s - sigma)) *
      (Real.log (p : ℝ) : ℂ) =
    -s * (Real.log (p : ℝ) : ℂ) by ring]
  exact (primeDirichletTerm_eq_exp_neg_mul_log p s).symm

theorem one_add_primeDirichletTerm_ne_zero
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) + primeDirichletTerm p s ≠ 0 := by
  intro h
  have heq : primeDirichletTerm p s = -1 := by linear_combination h
  have hnorm : ‖primeDirichletTerm p s‖ = 1 := by rw [heq, norm_neg, norm_one]
  have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpone
      (neg_neg_of_pos (zero_lt_one.trans hs))
  rw [norm_primeDirichletTerm] at hnorm
  linarith

theorem one_sub_primeDirichletTerm_ne_zero
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - primeDirichletTerm p s ≠ 0 := by
  intro h
  have heq : primeDirichletTerm p s = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖primeDirichletTerm p s‖ = 1 := by rw [heq, norm_one]
  have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpone
      (neg_neg_of_pos (zero_lt_one.trans hs))
  rw [norm_primeDirichletTerm] at hnorm
  linarith

/-- Safe correction times the actual source amplitude is exactly the reciprocal transfer. -/
theorem finiteMobiusPlueckerCorrection_mul_amplitude
    (S : Finset Nat.Primes) {sigma : ℝ} (hsigma : 1 < sigma)
    {s : ℂ} (hs : 1 < s.re) :
    finiteMobiusPlueckerCorrection S sigma s *
        finiteMobiusPlueckerAmplitude S sigma s =
      finiteMobiusPlueckerTransfer S sigma s := by
  classical
  rw [finiteMobiusPlueckerCorrection,
    finiteMobiusPlueckerAmplitude_eq_prod,
    finiteMobiusPlueckerTransfer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeDirichletTerm_two_mul, primeDirichletTerm_two_mul]
  have hsig : 1 < ((sigma : ℂ).re) := by simpa using hsigma
  have hplusSig := one_add_primeDirichletTerm_ne_zero p hsig
  have hplusS := one_add_primeDirichletTerm_ne_zero p hs
  have hminusS := one_sub_primeDirichletTerm_ne_zero p hs
  have hsqS : (1 : ℂ) - primeDirichletTerm p s ^ 2 ≠ 0 := by
    rw [show (1 : ℂ) - primeDirichletTerm p s ^ 2 =
      (1 - primeDirichletTerm p s) *
        (1 + primeDirichletTerm p s) by ring]
    exact mul_ne_zero hminusS hplusS
  rw [mobiusPlueckerEulerFactor]
  field_simp [hplusSig, hplusS, hminusS, hsqS]
  ring

/-- The fixed finite aperture has a nonzero limit at the Euler boundary. -/
theorem finiteMobiusPlueckerTransfer_one_ne_zero
    (S : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    finiteMobiusPlueckerTransfer S 1 s ≠ 0 := by
  classical
  rw [finiteMobiusPlueckerTransfer]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply div_ne_zero
  · intro h
    have heq : primeDirichletTerm p (1 : ℂ) = 1 :=
      (sub_eq_zero.mp h).symm
    have hnorm : ‖primeDirichletTerm p (1 : ℂ)‖ = 1 := by
      rw [heq, norm_one]
    have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    have hlt : (p : ℝ) ^ (-((1 : ℂ).re)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpone (by norm_num)
    rw [norm_primeDirichletTerm] at hnorm
    linarith
  · exact one_add_primeDirichletTerm_ne_zero p hs

theorem tendsto_finiteMobiusPlueckerTransfer_one
    (S : Finset Nat.Primes) (s : ℂ) :
    Tendsto (fun epsilon : ℝ =>
        finiteMobiusPlueckerTransfer S (1 + epsilon) s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (finiteMobiusPlueckerTransfer S 1 s)) := by
  apply Filter.Tendsto.mono_left _ inf_le_left
  have hcontinuous : Continuous (fun epsilon : ℝ =>
      finiteMobiusPlueckerTransfer S (1 + epsilon) s) := by
    simp only [finiteMobiusPlueckerTransfer]
    apply continuous_finsetProd
    intro p hp
    apply Continuous.div_const
    apply continuous_const.sub
    exact (continuous_primeDirichletTerm p).comp
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
  have hAt : Tendsto (fun epsilon : ℝ =>
      finiteMobiusPlueckerTransfer S (1 + epsilon) s)
      (𝓝 (0 : ℝ))
      (𝓝 (finiteMobiusPlueckerTransfer S (1 + 0) s)) :=
    hcontinuous.continuousAt
  simpa only [add_zero] using hAt

/-- Fixed prime aperture cannot have any finite Euler-normal limit. -/
theorem not_tendsto_finiteMobiusPlueckerTransfer_div_epsilon
    (S : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ¬ ∃ L : ℂ,
      Tendsto (fun epsilon : ℝ =>
          finiteMobiusPlueckerTransfer S (1 + epsilon) s /
            (epsilon : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hzero : Tendsto (fun epsilon : ℝ =>
      (epsilon : ℂ) *
        (finiteMobiusPlueckerTransfer S (1 + epsilon) s /
          (epsilon : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hepsilon.mul hL
  have heq : (fun epsilon : ℝ =>
      (epsilon : ℂ) *
        (finiteMobiusPlueckerTransfer S (1 + epsilon) s /
          (epsilon : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun epsilon : ℝ =>
        finiteMobiusPlueckerTransfer S (1 + epsilon) s) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hepsilon' : 0 < epsilon := hepsilon
    have hepsilonC : (epsilon : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hepsilon')
    field_simp [hepsilonC]
  have hzero' : Tendsto (fun epsilon : ℝ =>
      finiteMobiusPlueckerTransfer S (1 + epsilon) s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hzero.congr' heq
  have hone := tendsto_finiteMobiusPlueckerTransfer_one S s
  have heqzero : finiteMobiusPlueckerTransfer S 1 s = 0 :=
    tendsto_nhds_unique hone hzero'
  exact finiteMobiusPlueckerTransfer_one_ne_zero S hs heqzero

theorem mobiusPlueckerEulerFactor_sub_one
    (sigma : ℝ) (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    mobiusPlueckerEulerFactor sigma p s - 1 =
      -(primeDirichletTerm p (sigma : ℂ) + primeDirichletTerm p s) /
        (1 + primeDirichletTerm p s) := by
  rw [mobiusPlueckerEulerFactor]
  field_simp [one_add_primeDirichletTerm_ne_zero p hs]
  ring

/-- Fixed-`sigma` Euler products converge locally uniformly on `re s > 1`. -/
theorem multipliableLocallyUniformlyOn_mobiusPlueckerEulerFactor
    {sigma : ℝ} (hsigma : 1 < sigma) :
    MultipliableLocallyUniformlyOn
      (mobiusPlueckerEulerFactor sigma) mobiusPlueckerEulerDomain := by
  rw [multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn]
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (by simpa [mobiusPlueckerEulerDomain] using isOpen_lt continuous_const continuous_re)
  intro K hKU hK
  by_cases hKe : K = ∅
  · subst K
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  · obtain ⟨s₀, hs₀K, hs₀min⟩ :=
      hK.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hKe)
        continuous_re.continuousOn
    let a : ℝ := s₀.re
    have ha : 1 < a := hKU hs₀K
    let c : ℝ := 1 - (2 : ℝ) ^ (-a)
    have hc : 0 < c := by
      have hpow : (2 : ℝ) ^ (-a) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      dsimp [c]
      linarith
    let u : Nat.Primes → ℝ := fun p =>
      ((p : ℝ) ^ (-sigma) + (p : ℝ) ^ (-a)) / c
    have hu : Summable u := by
      apply Summable.div_const
      exact (Nat.Primes.summable_rpow.mpr (by linarith)).add
        (Nat.Primes.summable_rpow.mpr (by linarith))
    have hbound : ∀ p : Nat.Primes, ∀ s ∈ K,
        ‖mobiusPlueckerEulerFactor sigma p s - 1‖ ≤ u p := by
      intro p s hsK
      have hsU : 1 < s.re := hKU hsK
      have has : a ≤ s.re := hs₀min hsK
      have hpone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
      have hsbound : ‖primeDirichletTerm p s‖ ≤ (p : ℝ) ^ (-a) := by
        rw [norm_primeDirichletTerm]
        exact Real.rpow_le_rpow_of_exponent_le hpone (by linarith)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
      have hpbound : (p : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      have hden : c ≤ ‖(1 : ℂ) + primeDirichletTerm p s‖ := by
        have hrev := norm_sub_norm_le (1 : ℂ) (-primeDirichletTerm p s)
        have hmid : c ≤ 1 - ‖primeDirichletTerm p s‖ := by
          dsimp [c]
          nlinarith
        exact hmid.trans (by simpa using hrev)
      have hnum :
          ‖primeDirichletTerm p (sigma : ℂ) + primeDirichletTerm p s‖ ≤
            (p : ℝ) ^ (-sigma) + (p : ℝ) ^ (-a) := by
        calc
          _ ≤ ‖primeDirichletTerm p (sigma : ℂ)‖ +
              ‖primeDirichletTerm p s‖ := norm_add_le _ _
          _ ≤ _ := by
            rw [norm_primeDirichletTerm]
            simp only [ofReal_re]
            linarith
      rw [mobiusPlueckerEulerFactor_sub_one sigma p hsU, norm_div, norm_neg]
      have hnum0 : 0 ≤ (p : ℝ) ^ (-sigma) + (p : ℝ) ^ (-a) := by positivity
      exact div_le_div₀ hnum0 hnum hc hden
    have hcts : ∀ p : Nat.Primes,
        ContinuousOn (fun s => mobiusPlueckerEulerFactor sigma p s - 1) K := by
      intro p
      have hpcts : ContinuousOn (primeDirichletTerm p) K :=
        (continuous_primeDirichletTerm p).continuousOn
      have hnumcts : ContinuousOn
          (fun _s : ℂ => (1 : ℂ) - primeDirichletTerm p (sigma : ℂ)) K :=
        continuousOn_const
      have hdencts : ContinuousOn
          (fun s : ℂ => (1 : ℂ) + primeDirichletTerm p s) K :=
        continuousOn_const.add hpcts
      have hfac : ContinuousOn (mobiusPlueckerEulerFactor sigma p) K := by
        exact hnumcts.div hdencts
          (fun s hsK => one_add_primeDirichletTerm_ne_zero p (hKU hsK))
      exact hfac.sub continuousOn_const
    simpa [sub_eq_add_neg, add_assoc] using
      hu.hasProdUniformlyOn_one_add hK
        (Filter.Eventually.of_forall hbound) hcts

private theorem hasProd_inv₀
    {f : Nat.Primes → ℂ} {a : ℂ}
    (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun p => (f p)⁻¹) a⁻¹ := by
  rw [HasProd] at h ⊢
  simpa only [Finset.prod_inv_distrib] using h.inv₀ ha

/-- Closed form of the fixed-`sigma` Euler-product limit. -/
def mobiusPlueckerEulerLimit (sigma : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta (sigma : ℂ) *
    GaloisForLFunctions.squarefreePartition s)⁻¹

theorem mobiusPlueckerEulerFactor_hasProd
    {sigma : ℝ} (hsigma : 1 < sigma)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => mobiusPlueckerEulerFactor sigma p s)
      (mobiusPlueckerEulerLimit sigma s) := by
  have hsigRe : 1 < ((sigma : ℂ).re) := by simpa using hsigma
  have htwoRe : 1 < (2 * s).re := by simp; linarith
  have hzsig : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsigRe
  have hzs : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hz2s : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoRe
  have hsigInv := hasProd_inv₀
    (riemannZeta_eulerProduct_hasProd hsigRe) hzsig
  have hsInv := hasProd_inv₀
    (riemannZeta_eulerProduct_hasProd hs) hzs
  have h2sInv := hasProd_inv₀
    (riemannZeta_eulerProduct_hasProd htwoRe) hz2s
  have hquot := hsInv.mul (hasProd_inv₀ h2sInv (inv_ne_zero hz2s))
  have hprod := hsigInv.mul hquot
  have hfactor : ∀ p : Nat.Primes,
      (1 - ((p : ℂ) ^ (-(sigma : ℂ))))⁻¹⁻¹ *
          ((1 - ((p : ℂ) ^ (-s)))⁻¹⁻¹ *
            ((1 - ((p : ℂ) ^ (-(2 * s))))⁻¹⁻¹⁻¹)) =
        mobiusPlueckerEulerFactor sigma p s := by
    intro p
    simp only [inv_inv]
    change
      ((1 - primeDirichletTerm p (sigma : ℂ)) *
          ((1 - primeDirichletTerm p s) *
            (1 - primeDirichletTerm p (2 * s))⁻¹)) =
        mobiusPlueckerEulerFactor sigma p s
    rw [primeDirichletTerm_two_mul]
    have hplus := one_add_primeDirichletTerm_ne_zero p hs
    have hminus := one_sub_primeDirichletTerm_ne_zero p hs
    have hsq : (1 : ℂ) - primeDirichletTerm p s ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) - primeDirichletTerm p s ^ 2 =
        (1 - primeDirichletTerm p s) *
          (1 + primeDirichletTerm p s) by ring]
      exact mul_ne_zero hminus hplus
    rw [mobiusPlueckerEulerFactor]
    field_simp [hplus, hminus, hsq]
    ring
  have hprod' : HasProd
      (fun p : Nat.Primes => mobiusPlueckerEulerFactor sigma p s)
      ((riemannZeta (sigma : ℂ))⁻¹ *
        ((riemannZeta s)⁻¹ * (riemannZeta (2 * s))⁻¹⁻¹)) := by
    rw [HasProd] at hprod ⊢
    apply hprod.congr'
    filter_upwards with S
    exact Finset.prod_congr rfl (fun p _hp => hfactor p)
  convert hprod' using 1
  simp only [inv_inv]
  rw [mobiusPlueckerEulerLimit, GaloisForLFunctions.squarefreePartition]
  field_simp [hzsig, hzs, hz2s]

theorem mobiusPlueckerEulerFactor_hasProdLocallyUniformlyOn
    {sigma : ℝ} (hsigma : 1 < sigma) :
    HasProdLocallyUniformlyOn
      (mobiusPlueckerEulerFactor sigma)
      (mobiusPlueckerEulerLimit sigma)
      mobiusPlueckerEulerDomain := by
  exact
    (multipliableLocallyUniformlyOn_mobiusPlueckerEulerFactor hsigma).hasProdLocallyUniformlyOn.congr_right
      (fun s hs =>
        (mobiusPlueckerEulerFactor_hasProd hsigma hs).tprod_eq)

/-- Normal-cone continuation of the fixed-`sigma` Euler-product limit. -/
def mobiusPlueckerNormalConeLimit (sigma : ℝ) (s : ℂ) : ℂ :=
  mobiusCompletedNormalConeTransfer
    GaloisForLFunctions.squarefreePartition (sigma : ℂ) s

theorem mobiusPlueckerEulerLimit_div_epsilon
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {s : ℂ} (hs : 1 < s.re) :
    mobiusPlueckerEulerLimit (1 + epsilon) s / (epsilon : ℂ) =
      mobiusPlueckerNormalConeLimit (1 + epsilon) s := by
  symm
  rw [mobiusPlueckerNormalConeLimit,
    mobiusCompletedNormalConeTransfer_eq_div]
  · simp [separatedCompletedMobiusTransfer, mobiusPlueckerEulerLimit]
  · exact_mod_cast (by linarith : (1 + epsilon : ℝ) ≠ 1)
  · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  · exact GaloisForLFunctions.squarefreePartition_ne_zero hs

theorem continuousOn_inv_squarefreePartition :
    ContinuousOn
      (fun s : ℂ => (GaloisForLFunctions.squarefreePartition s)⁻¹)
      mobiusPlueckerEulerDomain := by
  intro s hs
  exact
    ((GaloisForLFunctions.differentiableAt_squarefreePartition hs).continuousAt.inv₀
      (GaloisForLFunctions.squarefreePartition_ne_zero hs)).continuousWithinAt

theorem tendstoLocallyUniformlyOn_mobiusPlueckerNormalConeLimit
    {epsilon : ℕ → ℝ}
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun n s => mobiusPlueckerNormalConeLimit (1 + epsilon n) s)
      (fun s => (GaloisForLFunctions.squarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain := by
  have hbase : Tendsto (fun n => (((1 + epsilon n : ℝ) : ℂ)))
      atTop (𝓝 (1 : ℂ)) := by
    have hepsilonC : Tendsto (fun n => (epsilon n : ℂ))
        atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hepsilon
    simpa using tendsto_const_nhds.add hepsilonC
  have hunit : Tendsto
      (fun n => zetaResidueUnit (((1 + epsilon n : ℝ) : ℂ)))
      atTop (𝓝 (1 : ℂ)) := by
    simpa [Function.comp_def] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hbase
  have hscalar : Tendsto
      (fun n => (zetaResidueUnit (((1 + epsilon n : ℝ) : ℂ)))⁻¹)
      atTop (𝓝 (1 : ℂ)) := by
    simpa using hunit.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hscalarLU : TendstoLocallyUniformlyOn
      (fun n (_s : ℂ) =>
        (zetaResidueUnit (((1 + epsilon n : ℝ) : ℂ)))⁻¹)
      (fun _s : ℂ => 1)
      atTop mobiusPlueckerEulerDomain :=
    (hscalar.tendstoUniformlyOn_const mobiusPlueckerEulerDomain).tendstoLocallyUniformlyOn
  have hfixed : TendstoLocallyUniformlyOn
      (fun (_n : ℕ) (_s : ℂ) =>
        (GaloisForLFunctions.squarefreePartition _s)⁻¹)
      (fun _s : ℂ =>
        (GaloisForLFunctions.squarefreePartition _s)⁻¹)
      atTop mobiusPlueckerEulerDomain := by
    intro u hu s hs
    exact ⟨mobiusPlueckerEulerDomain, self_mem_nhdsWithin,
      Filter.Eventually.of_forall (fun _n y hy => refl_mem_uniformity hu)⟩
  have hmul := hscalarLU.mul₀ hfixed continuousOn_const
    continuousOn_inv_squarefreePartition
  change TendstoLocallyUniformlyOn
      (fun n s =>
        (zetaResidueUnit (((1 + epsilon n : ℝ) : ℂ)))⁻¹ *
          (GaloisForLFunctions.squarefreePartition s)⁻¹)
      (fun s => 1 * (GaloisForLFunctions.squarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain at hmul
  have hmul' : TendstoLocallyUniformlyOn
      (fun n s =>
        (zetaResidueUnit (((1 + epsilon n : ℝ) : ℂ)))⁻¹ *
          (GaloisForLFunctions.squarefreePartition s)⁻¹)
      (fun s => (GaloisForLFunctions.squarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain := by
    simpa only [Pi.mul_apply, one_mul] using hmul
  exact hmul'.congr fun n s hs => by
    simp [mobiusPlueckerNormalConeLimit,
      mobiusCompletedNormalConeTransfer, mul_comm]

/-- Spectral half-plane as a locally compact sigma-compact source space. -/
abbrev MobiusPlueckerEulerPoint :=
  {s : ℂ // s ∈ mobiusPlueckerEulerDomain}

theorem isOpen_mobiusPlueckerEulerDomain :
    IsOpen mobiusPlueckerEulerDomain := by
  simpa [mobiusPlueckerEulerDomain] using
    isOpen_lt continuous_const continuous_re

noncomputable local instance : LocallyCompactSpace MobiusPlueckerEulerPoint :=
  isOpen_mobiusPlueckerEulerDomain.locallyCompactSpace

/-- A fixed compact exhaustion used only to diagonalize locally uniform Euler products. -/
noncomputable def mobiusPlueckerCompactExhaustion :
    CompactExhaustion MobiusPlueckerEulerPoint :=
  CompactExhaustion.choice MobiusPlueckerEulerPoint

theorem mem_primesBelowSubtype_iff
    {p : Nat.Primes} {N : ℕ} :
    p ∈ GaloisForLFunctions.primesBelowSubtype N ↔ (p : ℕ) < N := by
  constructor
  · intro hp
    rw [GaloisForLFunctions.primesBelowSubtype] at hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    have hval := congrArg (fun r : Nat.Primes => (r : ℕ)) hqp
    have hlt := (Nat.mem_primesBelow.mp q.property).1
    rw [← hval]
    exact hlt
  · intro hp
    rw [GaloisForLFunctions.primesBelowSubtype]
    let q : {a // a ∈ Nat.primesBelow N} :=
      ⟨(p : ℕ), Nat.mem_primesBelow.mpr ⟨hp, p.2⟩⟩
    apply Finset.mem_map.mpr
    exact ⟨q, by simp, Subtype.ext rfl⟩

theorem monotone_primesBelowSubtype :
    Monotone GaloisForLFunctions.primesBelowSubtype := by
  intro m n hmn p hp
  rw [mem_primesBelowSubtype_iff] at hp ⊢
  exact hp.trans_le hmn

theorem cofinal_primesBelowSubtype (p : Nat.Primes) :
    ∃ N, p ∈ GaloisForLFunctions.primesBelowSubtype N := by
  exact ⟨(p : ℕ) + 1,
    mem_primesBelowSubtype_iff.mpr (Nat.lt_succ_self _)⟩

/-- Quantitative compact-exhaustion diagonal lemma.  If `F n` differs from a locally uniformly
convergent family `G n` by less than `1/(n+1)` on the `n`-th compact, then `F n` has the same
locally uniform limit. -/
theorem tendstoLocallyUniformly_of_compactExhaustion_dist
    {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X)
    {F G : ℕ → X → ℂ} {f : X → ℂ}
    (hG : TendstoLocallyUniformly G f atTop)
    (hFG : ∀ n x, x ∈ K n →
      dist (G n x) (F n x) < (1 : ℝ) / (n + 1)) :
    TendstoLocallyUniformly F f atTop := by
  rw [Metric.tendstoLocallyUniformly_iff] at hG ⊢
  intro delta hdelta x
  obtain ⟨t, ht, hGt⟩ := hG (delta / 2) (by positivity) x
  obtain ⟨N, hKN⟩ := K.exists_mem_nhds x
  refine ⟨t ∩ K N, inter_mem ht hKN, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / (n + 1) < delta / 2 :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [hGt, eventually_ge_atTop N, hsmall] with n hnG hnN hnsmall
  intro y hy
  have hyKn : y ∈ K n := K.subset hnN hy.2
  calc
    dist (f y) (F n y) ≤
        dist (f y) (G n y) + dist (G n y) (F n y) :=
      dist_triangle _ _ _
    _ < delta / 2 + delta / 2 :=
      add_lt_add (hnG y hy.1) (hFG n y hyKn |>.trans hnsmall)
    _ = delta := by ring

/-- **Cofinal Möbius--Pluecker diagonal lift.**  Every positive critical sequence admits a nested
finite-prime exhaustion whose Euler-normal finite source transfers converge locally uniformly to
`1 / Z_sq` throughout `re s > 1`. -/
theorem exists_mobiusPlueckerDiagonal
    {epsilon : ℕ → ℝ}
    (hepsilonPos : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ S : ℕ → Finset Nat.Primes,
      Monotone S ∧
      (∀ p : Nat.Primes, ∃ n, p ∈ S n) ∧
      TendstoLocallyUniformlyOn
        (fun n s =>
          finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ))
        (fun s => (GaloisForLFunctions.squarefreePartition s)⁻¹)
        atTop mobiusPlueckerEulerDomain := by
  classical
  let K : CompactExhaustion MobiusPlueckerEulerPoint :=
    mobiusPlueckerCompactExhaustion
  have hstage : ∀ n, ∀ᶠ T : Finset Nat.Primes in atTop,
      ∀ x ∈ K n,
        dist (mobiusPlueckerEulerLimit (1 + epsilon n) x)
          (finiteMobiusPlueckerTransfer T (1 + epsilon n) x) <
            epsilon n / (n + 1) := by
    intro n
    have hsigma : 1 < 1 + epsilon n := by linarith [hepsilonPos n]
    have hprod :=
      mobiusPlueckerEulerFactor_hasProdLocallyUniformlyOn hsigma
    have hsub : TendstoLocallyUniformly
        (fun T : Finset Nat.Primes => fun x : MobiusPlueckerEulerPoint =>
          ∏ p ∈ T, mobiusPlueckerEulerFactor (1 + epsilon n) p x)
        (fun x : MobiusPlueckerEulerPoint =>
          mobiusPlueckerEulerLimit (1 + epsilon n) x)
        atTop := by
      rw [HasProdLocallyUniformlyOn,
        tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hprod
      change TendstoLocallyUniformly
        (fun T : Finset Nat.Primes => fun x : MobiusPlueckerEulerPoint =>
          ∏ p ∈ T, mobiusPlueckerEulerFactor (1 + epsilon n) p x)
        (fun x : MobiusPlueckerEulerPoint =>
          mobiusPlueckerEulerLimit (1 + epsilon n) x)
        atTop at hprod
      exact hprod
    have huniform : TendstoUniformlyOn
        (fun T : Finset Nat.Primes => fun x : MobiusPlueckerEulerPoint =>
          ∏ p ∈ T, mobiusPlueckerEulerFactor (1 + epsilon n) p x)
        (fun x : MobiusPlueckerEulerPoint =>
          mobiusPlueckerEulerLimit (1 + epsilon n) x)
        atTop (K n) :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hsub)
        (K n) (K.isCompact n)
    have htolerance : 0 < epsilon n / (n + 1 : ℝ) :=
      div_pos (hepsilonPos n) (by exact_mod_cast Nat.succ_pos n)
    have heventually :=
      Metric.tendstoUniformlyOn_iff.mp huniform
        (epsilon n / (n + 1 : ℝ)) htolerance
    filter_upwards [heventually] with T hT
    intro x hx
    simpa only [finiteMobiusPlueckerTransfer] using hT x hx
  choose B hB using fun n => Filter.eventually_atTop.mp (hstage n)
  let S : ℕ → Finset Nat.Primes := fun n =>
    (Finset.range (n + 1)).biUnion B ∪
      GaloisForLFunctions.primesBelowSubtype (n + 1)
  have hBsubset : ∀ n, B n ⊆ S n := by
    intro n p hp
    apply Finset.mem_union_left
    rw [Finset.mem_biUnion]
    exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hp⟩
  have hSmono : Monotone S := by
    intro m n hmn p hp
    rcases Finset.mem_union.mp hp with hpB | hpPrime
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion] at hpB ⊢
      obtain ⟨k, hkm, hpk⟩ := hpB
      exact ⟨k, Finset.mem_range.mpr
        ((Finset.mem_range.mp hkm).trans_le (Nat.succ_le_succ hmn)), hpk⟩
    · apply Finset.mem_union_right
      exact monotone_primesBelowSubtype (Nat.succ_le_succ hmn) hpPrime
  have hScofinal : ∀ p : Nat.Primes, ∃ n, p ∈ S n := by
    intro p
    refine ⟨(p : ℕ), Finset.mem_union_right _ ?_⟩
    exact mem_primesBelowSubtype_iff.mpr (Nat.lt_succ_self _)
  have happrox : ∀ n x, x ∈ K n →
      dist (mobiusPlueckerNormalConeLimit (1 + epsilon n) x)
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) x /
          (epsilon n : ℂ)) <
        (1 : ℝ) / (n + 1) := by
    intro n x hx
    have hraw := hB n (S n) (hBsubset n) x hx
    rw [← mobiusPlueckerEulerLimit_div_epsilon
      (hepsilonPos n) x.property]
    rw [dist_eq_norm, div_sub_div_same, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hepsilonPos n)]
    apply (div_lt_iff₀ (hepsilonPos n)).2
    simpa only [dist_eq_norm, div_eq_mul_inv, mul_comm, one_mul] using hraw
  have hcentralSub : TendstoLocallyUniformly
      (fun n (x : MobiusPlueckerEulerPoint) =>
        mobiusPlueckerNormalConeLimit (1 + epsilon n) x)
      (fun x : MobiusPlueckerEulerPoint =>
        (GaloisForLFunctions.squarefreePartition x)⁻¹)
      atTop := by
    have hcentral :=
      tendstoLocallyUniformlyOn_mobiusPlueckerNormalConeLimit hepsilonZero
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      at hcentral
    change TendstoLocallyUniformly
      (fun n (x : MobiusPlueckerEulerPoint) =>
        mobiusPlueckerNormalConeLimit (1 + epsilon n) x)
      (fun x : MobiusPlueckerEulerPoint =>
        (GaloisForLFunctions.squarefreePartition x)⁻¹)
      atTop at hcentral
    exact hcentral
  have hdiagonalSub : TendstoLocallyUniformly
      (fun n (x : MobiusPlueckerEulerPoint) =>
        finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) x /
          (epsilon n : ℂ))
      (fun x : MobiusPlueckerEulerPoint =>
        (GaloisForLFunctions.squarefreePartition x)⁻¹)
      atTop :=
    tendstoLocallyUniformly_of_compactExhaustion_dist K
      hcentralSub happrox
  refine ⟨S, hSmono, hScofinal, ?_⟩
  exact
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
      hdiagonalSub

/-- Gamma completion `X_sq = C · Z_sq` on the Euler half-plane. -/
def mobiusPlueckerCompletedSquarefreePartition (s : ℂ) : ℂ :=
  archFactor s * GaloisForLFunctions.squarefreePartition s

theorem archFactor_ne_zero_on_mobiusPlueckerEulerDomain
    {s : ℂ} (hs : s ∈ mobiusPlueckerEulerDomain) :
    archFactor s ≠ 0 := by
  apply archFactor_ne_zero
  · intro hs0
    rw [hs0] at hs
    norm_num [mobiusPlueckerEulerDomain] at hs
  · intro hs1
    rw [hs1] at hs
    norm_num [mobiusPlueckerEulerDomain] at hs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos
      (lt_trans zero_lt_one hs)

theorem continuousOn_inv_archFactor_mobiusPlueckerEulerDomain :
    ContinuousOn (fun s : ℂ => (archFactor s)⁻¹)
      mobiusPlueckerEulerDomain := by
  intro s hs
  have hGammaNe : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hGamma : AnalyticAt ℂ Complex.Gammaℝ s :=
    Gammaℝ_analyticAt hGammaNe
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by
    fun_prop
  have harch : AnalyticAt ℂ archFactor s := by
    unfold archFactor
    exact hpoly.mul hGamma
  exact (harch.continuousAt.inv₀
    (archFactor_ne_zero_on_mobiusPlueckerEulerDomain hs)).continuousWithinAt

/-- Multiplying a reciprocal-squarefree diagonal by the nonvanishing inverse archimedean factor
gives the Gamma-completed exceptional lift, locally uniformly on the same half-plane. -/
theorem TendstoLocallyUniformlyOn.mobiusPlueckerGammaCompleted
    {epsilon : ℕ → ℝ} {S : ℕ → Finset Nat.Primes}
    (h : TendstoLocallyUniformlyOn
      (fun n s =>
        finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ))
      (fun s => (GaloisForLFunctions.squarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain) :
    TendstoLocallyUniformlyOn
      (fun n s => (archFactor s)⁻¹ *
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ)))
      (fun s => (mobiusPlueckerCompletedSquarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain := by
  have harchFixed : TendstoLocallyUniformlyOn
      (fun (_n : ℕ) (s : ℂ) => (archFactor s)⁻¹)
      (fun s : ℂ => (archFactor s)⁻¹)
      atTop mobiusPlueckerEulerDomain := by
    intro u hu s hs
    exact ⟨mobiusPlueckerEulerDomain, self_mem_nhdsWithin,
      Filter.Eventually.of_forall (fun _n y hy => refl_mem_uniformity hu)⟩
  have hmul := harchFixed.mul₀ h
    continuousOn_inv_archFactor_mobiusPlueckerEulerDomain
    continuousOn_inv_squarefreePartition
  change TendstoLocallyUniformlyOn
      (fun n s => (archFactor s)⁻¹ *
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ)))
      (fun s => (archFactor s)⁻¹ *
        (GaloisForLFunctions.squarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain at hmul
  exact hmul.congr_right fun s hs => by
    simp [mobiusPlueckerCompletedSquarefreePartition, mul_comm]

/-- Projectivizing the Gamma-completed diagonal gives the exact negative reciprocal-square
horizon transition `-X_sq⁻²`. -/
theorem TendstoLocallyUniformlyOn.mobiusPlueckerProjectivizedSquare
    {epsilon : ℕ → ℝ} {S : ℕ → Finset Nat.Primes}
    (h : TendstoLocallyUniformlyOn
      (fun n s => (archFactor s)⁻¹ *
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ)))
      (fun s => (mobiusPlueckerCompletedSquarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain) :
    TendstoLocallyUniformlyOn
      (fun n s => -((archFactor s)⁻¹ *
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ))) ^ 2)
      (fun s => -(mobiusPlueckerCompletedSquarefreePartition s)⁻¹ ^ 2)
      atTop mobiusPlueckerEulerDomain := by
  have htarget : ContinuousOn
      (fun s => (mobiusPlueckerCompletedSquarefreePartition s)⁻¹)
      mobiusPlueckerEulerDomain := by
    intro s hs
    have hmul := (continuousOn_inv_squarefreePartition s hs).mul
      (continuousOn_inv_archFactor_mobiusPlueckerEulerDomain s hs)
    change ContinuousWithinAt
      (fun z => (GaloisForLFunctions.squarefreePartition z)⁻¹ *
        (archFactor z)⁻¹) mobiusPlueckerEulerDomain s at hmul
    simpa only [mobiusPlueckerCompletedSquarefreePartition,
      mul_inv_rev] using hmul
  have hsq := h.mul₀ h htarget htarget
  change TendstoLocallyUniformlyOn
      (fun n s =>
        ((archFactor s)⁻¹ *
          (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ))) *
        ((archFactor s)⁻¹ *
          (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ))))
      (fun s => (mobiusPlueckerCompletedSquarefreePartition s)⁻¹ *
        (mobiusPlueckerCompletedSquarefreePartition s)⁻¹)
      atTop mobiusPlueckerEulerDomain at hsq
  have hsq' := hsq.neg
  change TendstoLocallyUniformlyOn
      (fun n s => -(((archFactor s)⁻¹ *
        (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
          (epsilon n : ℂ))) *
        ((archFactor s)⁻¹ *
          (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ)))))
      (fun s => -((mobiusPlueckerCompletedSquarefreePartition s)⁻¹ *
        (mobiusPlueckerCompletedSquarefreePartition s)⁻¹))
      atTop mobiusPlueckerEulerDomain at hsq'
  simpa only [pow_two] using hsq'

/-- Full exact package: nested cofinal prime sets, reciprocal limit, Gamma completion, and its
projectivized negative square all use one and the same finite-source diagonal. -/
theorem exists_mobiusPlueckerCompletedDiagonal
    {epsilon : ℕ → ℝ}
    (hepsilonPos : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ S : ℕ → Finset Nat.Primes,
      Monotone S ∧
      (∀ p : Nat.Primes, ∃ n, p ∈ S n) ∧
      TendstoLocallyUniformlyOn
        (fun n s =>
          finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ))
        (fun s => (GaloisForLFunctions.squarefreePartition s)⁻¹)
        atTop mobiusPlueckerEulerDomain ∧
      TendstoLocallyUniformlyOn
        (fun n s => (archFactor s)⁻¹ *
          (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ)))
        (fun s => (mobiusPlueckerCompletedSquarefreePartition s)⁻¹)
        atTop mobiusPlueckerEulerDomain ∧
      TendstoLocallyUniformlyOn
        (fun n s => -((archFactor s)⁻¹ *
          (finiteMobiusPlueckerTransfer (S n) (1 + epsilon n) s /
            (epsilon n : ℂ))) ^ 2)
        (fun s => -(mobiusPlueckerCompletedSquarefreePartition s)⁻¹ ^ 2)
        atTop mobiusPlueckerEulerDomain := by
  obtain ⟨S, hmono, hcofinal, hdiag⟩ :=
    exists_mobiusPlueckerDiagonal hepsilonPos hepsilonZero
  have hcompleted :=
    TendstoLocallyUniformlyOn.mobiusPlueckerGammaCompleted hdiag
  exact ⟨S, hmono, hcofinal, hdiag, hcompleted,
    TendstoLocallyUniformlyOn.mobiusPlueckerProjectivizedSquare hcompleted⟩

end RHTower
