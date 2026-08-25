import GaloisForLFunctions.RHTower.PrimeSourceCancellationBudget
import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection
import GaloisForLFunctions.RHTower.WeightedEulerFECarrierSeparation
import GaloisForLFunctions.RHTower.EulerSourceJetOpenness
import GaloisForLFunctions.HTGeometry.HolomorphicOnOpen
import GaloisForLFunctions.HTGeometry.CompactOpenDualCarrier
import GaloisForLFunctions.HTGeometry.CarrierComplexFunctional
import GaloisForLFunctions.HTGeometry.ConvexCarrierCauchyVanishing
import GaloisForLFunctions.HTGeometry.CarrierAnnihilatesHolomorphicPompeiu
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual
import GaloisForLFunctions.HTGeometry.SymmetricMultilinearDiagonalHasse

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Entire prime exponential in logarithmic coordinates. -/
def primeExponential (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * s)

theorem primeExponential_eq_cpow (p : Nat.Primes) (s : ℂ) :
    primeExponential p s = ((p : ℕ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr p.2.ne_zero)]
  unfold primeExponential
  congr 1
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (p : ℕ))]
  push_cast
  ring

/-- Prime exponential restricted to a domain. -/
def primeExponentialMapOn (D : Set ℂ) (p : Nat.Primes) : C(D, ℂ) :=
  ⟨fun z => primeExponential p (z : ℂ), by
    unfold primeExponential
    fun_prop⟩

theorem primeExponentialMapOn_mem (D : Set ℂ) (p : Nat.Primes) :
    primeExponentialMapOn D p ∈ holoOn D := by
  refine ⟨primeExponential p, ?_, fun _ => rfl⟩
  unfold primeExponential
  fun_prop

/-- Prime exponential as an element of the compact-open holomorphic space. -/
def primeExponentialOn (D : Set ℂ) (p : Nat.Primes) : holoOn D :=
  ⟨primeExponentialMapOn D p, primeExponentialMapOn_mem D p⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Cofinite annihilation of prime exponentials kills every compact-open continuous functional. -/
theorem holoOn_eq_zero_of_annihilates_primeExponential
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (S : Finset Nat.Primes) (ell : holoOn D →L[ℝ] ℝ)
    (hann : ∀ p : Nat.Primes, p ∉ S →
      ell (primeExponentialOn D p) = 0 ∧
        ell (holoOnImul D (primeExponentialOn D p)) = 0) :
    ∀ y : holoOn D, ell y = 0 := by
  classical
  obtain ⟨K₀, C₀, hK₀, hC₀, hbnd⟩ := exists_compact_dual_bound (holoOn D) ell
  set K₁ : Set ℂ := (Subtype.val : ↥D → ℂ) '' K₀ with hK₁def
  have hK₁ : IsCompact K₁ := hK₀.image continuous_subtype_val
  have hK₁D : K₁ ⊆ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨K, hKcompact, hKconv, hK₁K, hKD⟩ :=
    exists_compact_convex_between hK₁ hDopen hDconv hK₁D
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  set T : holoOn D →ₗ[ℝ] C(K, ℂ) := holoOnRestrict hKD with hT
  have hbd : ∀ g : holoOn D, |ell.toLinearMap g| ≤ C₀ * ‖T g‖ := by
    intro g
    refine hbnd g ‖T g‖ (norm_nonneg _) ?_
    intro x hx
    have hmem : ((x : ℂ)) ∈ K := hK₁K ⟨x, hx, rfl⟩
    have hxeq : (⟨(x : ℂ), hKD hmem⟩ : (D : Set ℂ)) = x := Subtype.ext rfl
    have hval : (g : C((D : Set ℂ), ℂ)) x = T g ⟨(x : ℂ), hmem⟩ := by
      rw [hT, holoOnRestrict_apply, hxeq]
    rw [hval]
    exact (T g).norm_coe_le_norm _
  obtain ⟨L, hL⟩ := exists_complex_functional_of_bound (M := ↥(holoOn D)) (K := ↥K)
    T ell.toLinearMap C₀ hbd
  have hLann : ∀ p : Nat.Primes, p ∉ S → L (T (primeExponentialOn D p)) = 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hann p hp
    have hre : (L (T (primeExponentialOn D p))).re = 0 := by
      rw [hL (primeExponentialOn D p)]
      exact h1
    have hTi : T (holoOnImul D (primeExponentialOn D p)) =
        Complex.I • T (primeExponentialOn D p) := rfl
    have him : (Complex.I * L (T (primeExponentialOn D p))).re = 0 := by
      have := hL (holoOnImul D (primeExponentialOn D p))
      rw [hTi, map_smul, smul_eq_mul] at this
      rw [this]
      exact h2
    rw [Complex.mul_re] at him
    simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_eq_zero] at him
    exact Complex.ext hre him
  have hTe : ∀ p : Nat.Primes,
      T (primeExponentialOn D p) =
        compactExponentialTest (coordMap K) ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro p
    ext z
    rw [hT, holoOnRestrict_apply, compactExponentialTest_apply]
    rfl
  set F : ℂ → ℂ := compactFourierBorel L (coordMap K) with hF
  have hFdiff : Differentiable ℂ F := by
    intro z
    exact ((compactFourierBorel_analyticOnNhd L (coordMap K)) z (Set.mem_univ z)).differentiableAt
  set A : ℝ := ‖coordMap K‖ with hAdef
  set C : ℝ := max 1 ‖L‖ with hCdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hFgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖) := by
    intro z
    rw [hF, hAdef, hCdef]
    exact le_trans (norm_compactFourierBorel_le_exp L (coordMap K) z)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))
  set E : Finset ℕ := S.map ⟨fun q : Nat.Primes => (q : ℕ), Subtype.val_injective⟩ with hE
  have hFprime : ∀ p : ℕ, p.Prime → p ∉ E →
      F ((Real.log (p : ℝ) : ℝ) : ℂ) = 0 := by
    intro p hp hpE
    let q : Nat.Primes := ⟨p, hp⟩
    have hqS : q ∉ S := by
      intro hq
      apply hpE
      rw [hE]
      exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hF]
    change L (compactExponentialTest (coordMap K)
      ((Real.log (((q : Nat.Primes) : ℕ) : ℝ) : ℝ) : ℂ)) = 0
    rw [← hTe q]
    exact hLann q hqS
  have hFzero : F = 0 :=
    GaloisForLFunctions.RHTower.PrimeCancellation.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
        hFdiff hA hC hFgrow E hFprime
  have hpow : ∀ N : ℕ, L (coordMap K ^ N) = 0 :=
    fun N => map_coordinate_pow_eq_zero_of_fourierBorel_zero L (coordMap K)
      (fun z => by simpa [hF] using congrFun hFzero z) N
  have hzero := cauchyTransform_eq_zero_of_convex hKcompact hKconv L hpow
  intro y
  obtain ⟨G, hG, hGy⟩ := y.2
  have hTy : ∀ z : K, T y z = G (z : ℂ) := by
    intro z
    rw [hT, holoOnRestrict_apply]
    exact hGy _
  have hLy := apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen (K := K)
    hKcompact hDopen hKD hG L hzero (T y) hTy
  have hfin := hL y
  rw [hLy] at hfin
  simpa using hfin.symm

/-- Retained prime exponentials and their imaginary multiples. -/
def primeExponentialOnFamily (D : Set ℂ) (S : Finset Nat.Primes) :
    {p : Nat.Primes // p ∉ S} × Bool → holoOn D :=
  fun q => if q.2 then holoOnImul D (primeExponentialOn D (q.1 : Nat.Primes))
    else primeExponentialOn D (q.1 : Nat.Primes)

/-- Cofinite prime exponentials have dense complex span in the compact-open holomorphic space. -/
theorem topologicalClosure_span_primeExponentialOn_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (S : Finset Nat.Primes) :
    (Submodule.span ℝ (Set.range (primeExponentialOnFamily D S))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (Submodule.span ℝ (Set.range (primeExponentialOnFamily D S))) ?_
  intro ell hell
  have hann : ∀ p : Nat.Primes, p ∉ S →
      ell (primeExponentialOn D p) = 0 ∧
        ell (holoOnImul D (primeExponentialOn D p)) = 0 := by
    intro p hp
    constructor
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, false), ?_⟩)
      simp [primeExponentialOnFamily]
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, true), ?_⟩)
      simp [primeExponentialOnFamily]
  exact ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_primeExponential hDopen hDconv S ell hann)

/-- A continuous real functional on a product of complex lines only sees finitely many
coordinates. -/
theorem realContinuousDual_pi_hasFiniteSupport
    {I : Type*} (L : (I → ℂ) →L[ℝ] ℝ) :
    ∃ S : Finset I, ∀ x : I → ℂ, (∀ i ∈ S, x i = 0) → L x = 0 := by
  classical
  have hball : Metric.ball (0 : ℝ) 1 ∈ nhds (L 0) := by
    simpa using Metric.ball_mem_nhds (0 : ℝ) zero_lt_one
  have hpre : L ⁻¹' Metric.ball (0 : ℝ) 1 ∈ nhds (0 : I → ℂ) :=
    L.continuous.continuousAt hball
  rw [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hpre
  obtain ⟨S, U, hU, hsub⟩ := hpre
  refine ⟨S, fun x hx => ?_⟩
  by_contra hLx
  let c : ℝ := (L x)⁻¹
  have hcx : c • x ∈ Set.pi (S : Set I) U := by
    intro i hi
    have hzero : (0 : ℂ) ∈ U i := mem_of_mem_nhds (hU i)
    simpa [Pi.smul_apply, hx i hi] using hzero
  have hcball : L (c • x) ∈ Metric.ball (0 : ℝ) 1 := hsub hcx
  have hnorm : |L (c • x)| < 1 := by
    simpa [Real.dist_eq] using hcball
  rw [L.map_smul] at hnorm
  change |c * L x| < 1 at hnorm
  rw [show c * L x = 1 by exact inv_mul_cancel₀ hLx] at hnorm
  norm_num at hnorm

/-- Product-topology coefficient vector concentrated at one prime. -/
noncomputable def primeCoefficientGenerator (p : Nat.Primes) : Nat.Primes → ℂ :=
  Pi.single p 1

/-- A complex coefficient acts through its real and imaginary prime-exponential directions. -/
def complexCoefficientPrimeExponentialMap (D : Set ℂ) (p : Nat.Primes) :
    ℂ →ₗ[ℝ] holoOn D where
  toFun c := c.re • primeExponentialOn D p +
    c.im • holoOnImul D (primeExponentialOn D p)
  map_add' c d := by
    apply Subtype.ext
    ext z
    simp [add_smul]
    ring
  map_smul' r c := by
    apply Subtype.ext
    ext z
    simp [Complex.real_smul]
    ring

/-- Finite-support linear coefficient map into compact-open holomorphic functions. -/
def primeExponentialCoefficientMap (D : Set ℂ) :
    (Nat.Primes →₀ ℂ) →ₗ[ℝ] holoOn D :=
  (Finsupp.lsum ℝ) (fun p => complexCoefficientPrimeExponentialMap D p)

@[simp] theorem primeExponentialCoefficientMap_single
    (D : Set ℂ) (p : Nat.Primes) (c : ℂ) :
    primeExponentialCoefficientMap D (Finsupp.single p c) =
      c.re • primeExponentialOn D p +
        c.im • holoOnImul D (primeExponentialOn D p) := by
  exact Finsupp.lsum_single ℝ (fun p => complexCoefficientPrimeExponentialMap D p) p c

/-- Finite-support coefficients embedded in their unrestricted product completion. -/
def primeCoefficientProfile :
    (Nat.Primes →₀ ℂ) →ₗ[ℝ] (Nat.Primes → ℂ) where
  toFun a p := a p
  map_add' a b := by funext p; simp
  map_smul' r a := by funext p; rfl

@[simp] theorem primeCoefficientProfile_single
    (p : Nat.Primes) (c : ℂ) :
    primeCoefficientProfile (Finsupp.single p c) = Pi.single p c := by
  funext q
  classical
  by_cases hqp : q = p
  · subst q
    simp [primeCoefficientProfile]
  · simp [primeCoefficientProfile, hqp]

/-- Graph of finite prime coefficients and their linear prime-exponential response. -/
def primeExponentialCoefficientGraphMap (D : Set ℂ) :
    (Nat.Primes →₀ ℂ) →ₗ[ℝ]
      (holoOn D × (Nat.Primes → ℂ)) :=
  ((primeExponentialCoefficientMap D).prod primeCoefficientProfile)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Graph of the finite-support linear coefficient map is dense in the independent product of
compact-open holomorphic functions and unrestricted prime coefficients. -/
theorem topologicalClosure_primeExponentialCoefficientGraph_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) :
    (LinearMap.range (primeExponentialCoefficientGraphMap D)).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_pair_dual_eq_zero_lcs
    (E := holoOn D) (F := Nat.Primes → ℂ)
    (LinearMap.range (primeExponentialCoefficientGraphMap D)) ?_
  intro fH fC hann
  have hgraphReal : ∀ p : Nat.Primes,
      fH (primeExponentialOn D p) + fC (primeCoefficientGenerator p) = 0 := by
    intro p
    have h := hann (primeExponentialCoefficientGraphMap D (Finsupp.single p 1))
      ⟨Finsupp.single p 1, rfl⟩
    simpa [primeExponentialCoefficientGraphMap, primeCoefficientGenerator] using h
  have hgraphImag : ∀ p : Nat.Primes,
      fH (holoOnImul D (primeExponentialOn D p)) +
        fC (Complex.I • primeCoefficientGenerator p) = 0 := by
    intro p
    have hsingle : Pi.single p Complex.I =
        Complex.I • (Pi.single p 1 : Nat.Primes → ℂ) := by
      funext q
      classical
      by_cases hqp : q = p
      · subst q
        simp
      · simp [hqp]
    have h := hann (primeExponentialCoefficientGraphMap D (Finsupp.single p Complex.I))
      ⟨Finsupp.single p Complex.I, rfl⟩
    simpa [primeExponentialCoefficientGraphMap, primeCoefficientGenerator, hsingle] using h
  obtain ⟨S, hS⟩ := realContinuousDual_pi_hasFiniteSupport fC
  have hfCreal : ∀ p : Nat.Primes, p ∉ S → fC (primeCoefficientGenerator p) = 0 := by
    intro p hp
    apply hS
    intro q hq
    have hpq : p ≠ q := fun hpq => hp (hpq ▸ hq)
    simp [primeCoefficientGenerator, hpq.symm]
  have hfCimag : ∀ p : Nat.Primes, p ∉ S →
      fC (Complex.I • primeCoefficientGenerator p) = 0 := by
    intro p hp
    apply hS
    intro q hq
    have hpq : p ≠ q := fun hpq => hp (hpq ▸ hq)
    simp [primeCoefficientGenerator, hpq.symm]
  have hfHann : ∀ p : Nat.Primes, p ∉ S →
      fH (primeExponentialOn D p) = 0 ∧
        fH (holoOnImul D (primeExponentialOn D p)) = 0 := by
    intro p hp
    constructor
    · simpa [hfCreal p hp] using hgraphReal p
    · simpa [hfCimag p hp] using hgraphImag p
  have hfH : ∀ y : holoOn D, fH y = 0 :=
    holoOn_eq_zero_of_annihilates_primeExponential hDopen hDconv S fH hfHann
  have hfC : ∀ x : Nat.Primes → ℂ, fC x = 0 := by
    intro x
    let a : Nat.Primes →₀ ℂ := Finsupp.onFinset S
      (fun p => if p ∈ S then x p else 0) (by
        intro p hp
        by_contra hpS
        exact hp (by simp [hpS]))
    have haCoord : ∀ p ∈ S, primeCoefficientProfile a p = x p := by
      intro p hp
      simp [a, primeCoefficientProfile, hp]
    have htail : fC (x - primeCoefficientProfile a) = 0 := by
      apply hS
      intro p hp
      simp [haCoord p hp]
    have haGraph := hann (primeExponentialCoefficientGraphMap D a) ⟨a, rfl⟩
    have haZero : fC (primeCoefficientProfile a) = 0 := by
      simpa [primeExponentialCoefficientGraphMap, hfH] using haGraph
    simpa [map_sub, haZero] using htail
  exact ⟨hfH, hfC⟩

/-- The finite-support prime-exponential coefficient map itself has dense range. -/
theorem topologicalClosure_range_primeExponentialCoefficientMap_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) :
    (LinearMap.range (primeExponentialCoefficientMap D)).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (LinearMap.range (primeExponentialCoefficientMap D)) ?_
  intro ell hell
  have hann : ∀ p : Nat.Primes,
      ell (primeExponentialOn D p) = 0 ∧
        ell (holoOnImul D (primeExponentialOn D p)) = 0 := by
    intro p
    constructor
    · have h := hell (primeExponentialCoefficientMap D (Finsupp.single p 1))
          ⟨Finsupp.single p 1, rfl⟩
      simpa using h
    · have h := hell (primeExponentialCoefficientMap D (Finsupp.single p Complex.I))
          ⟨Finsupp.single p Complex.I, rfl⟩
      simpa using h
  exact ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_primeExponential hDopen hDconv ∅ ell
      (fun p _ => hann p))

/-! ## Nonlinear Euler log-flux analytic germs -/

/-- Pointwise complex scalar multiplication preserves the compact-open holomorphic subspace. -/
noncomputable instance instSMulComplexHoloOn (D : Set ℂ) : SMul ℂ (holoOn D) where
  smul c f := ⟨c • (f : C(D, ℂ)), by
    obtain ⟨F, hF, hf⟩ := f.2
    exact ⟨fun z => c * F z, (differentiableOn_const c).mul hF,
      fun z => by simp [hf z]⟩⟩

/-- Complex module structure on compact-open holomorphic functions. -/
noncomputable instance instModuleComplexHoloOn (D : Set ℂ) : Module ℂ (holoOn D) :=
  Function.Injective.module ℂ (M := C(D, ℂ)) (M₂ := holoOn D)
    (holoOn D).subtype.toAddHom Subtype.val_injective
    (fun (_ : ℂ) (_ : holoOn D) => rfl)

theorem complex_smul_primeExponentialOn
    (D : Set ℂ) (p : Nat.Primes) (c : ℂ) :
    c • primeExponentialOn D p =
      c.re • primeExponentialOn D p +
        c.im • holoOnImul D (primeExponentialOn D p) := by
  apply Subtype.ext
  ext z
  change c * primeExponential p z =
    (c.re : ℂ) * primeExponential p z +
      (c.im : ℂ) * (Complex.I * primeExponential p z)
  nth_rewrite 1 [← Complex.re_add_im c]
  ring

/-- One weighted prime tangent coefficient `c ↦ (log p)c p^{-s}`. -/
def complexCoefficientPrimeEulerFluxTangentMap (D : Set ℂ) (p : Nat.Primes) :
    ℂ →ₗ[ℝ] holoOn D where
  toFun c := (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * c) • primeExponentialOn D p
  map_add' c d := by
    apply Subtype.ext
    ext z
    change (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * (c + d)) * primeExponential p z =
      (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * c) * primeExponential p z +
        (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * d) * primeExponential p z
    ring
  map_smul' r c := by
    apply Subtype.ext
    ext z
    change (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * ((r : ℂ) * c)) *
      primeExponential p z =
        (r : ℂ) * ((((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * c) *
          primeExponential p z)
    ring

/-- Differential at zero of the finite-support nonlinear Euler flux chart. -/
def primeEulerFluxTangentCoefficientMap (D : Set ℂ) :
    (Nat.Primes →₀ ℂ) →ₗ[ℝ] holoOn D :=
  (Finsupp.lsum ℝ) (fun p => complexCoefficientPrimeEulerFluxTangentMap D p)

@[simp] theorem primeEulerFluxTangentCoefficientMap_single
    (D : Set ℂ) (p : Nat.Primes) (c : ℂ) :
    primeEulerFluxTangentCoefficientMap D (Finsupp.single p c) =
      (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * c) • primeExponentialOn D p := by
  exact Finsupp.lsum_single ℝ (fun p => complexCoefficientPrimeEulerFluxTangentMap D p) p c

/-- The weighted Euler-flux tangent map has dense range; nonzero logarithmic prime weights do not
change the cofinite prime-exponential completeness theorem. -/
theorem topologicalClosure_range_primeEulerFluxTangentCoefficientMap_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) :
    (LinearMap.range (primeEulerFluxTangentCoefficientMap D)).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (LinearMap.range (primeEulerFluxTangentCoefficientMap D)) ?_
  intro ell hell
  have hann : ∀ p : Nat.Primes,
      ell (primeExponentialOn D p) = 0 ∧
        ell (holoOnImul D (primeExponentialOn D p)) = 0 := by
    intro p
    have hlog : Real.log ((p : ℕ) : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
    have hlogC : (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) ≠ 0 :=
      ofReal_ne_zero.mpr hlog
    let r : ℂ := (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ))⁻¹
    have hr : (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) * r = 1 := by
      exact mul_inv_cancel₀ hlogC
    constructor
    · have h := hell
          (primeEulerFluxTangentCoefficientMap D (Finsupp.single p r))
          ⟨Finsupp.single p r, rfl⟩
      have hmap : primeEulerFluxTangentCoefficientMap D (Finsupp.single p r) =
          primeExponentialOn D p := by
        rw [primeEulerFluxTangentCoefficientMap_single, hr, one_smul]
      rwa [hmap] at h
    · have h := hell
          (primeEulerFluxTangentCoefficientMap D (Finsupp.single p (Complex.I * r)))
          ⟨Finsupp.single p (Complex.I * r), rfl⟩
      have hmap : primeEulerFluxTangentCoefficientMap D (Finsupp.single p (Complex.I * r)) =
          holoOnImul D (primeExponentialOn D p) := by
        rw [primeEulerFluxTangentCoefficientMap_single]
        have hscalar : (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) * (Complex.I * r) =
            Complex.I := by
          calc
            (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) * (Complex.I * r) =
                Complex.I * ((((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) * r) := by ring
            _ = Complex.I := by rw [hr, mul_one]
        rw [hscalar]
        rfl
      rwa [hmap] at h
  exact ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_primeExponential hDopen hDconv ∅ ell
      (fun p _ => hann p))

/-- The `k`th prime-power exponential `p^(-k s)`. -/
def primePowerExponential (p : Nat.Primes) (k : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-((k : ℂ) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) * s)

theorem primePowerExponential_eq_cpow (p : Nat.Primes) (k : ℕ) (s : ℂ) :
    primePowerExponential p k s = ((p : ℕ) : ℂ) ^ (-(k : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr p.2.ne_zero)]
  unfold primePowerExponential
  congr 1
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (p : ℕ))]
  push_cast
  ring

/-- Prime-power exponential restricted to a compact-open holomorphic domain. -/
def primePowerExponentialOn (D : Set ℂ) (p : Nat.Primes) (k : ℕ) : holoOn D := by
  refine ⟨⟨fun z => primePowerExponential p k (z : ℂ), ?_⟩, ?_⟩
  · unfold primePowerExponential
    fun_prop
  · refine ⟨primePowerExponential p k, ?_, fun _ => rfl⟩
    unfold primePowerExponential
    fun_prop

/-- Actual nonlinear finite-support Euler flux, using the corpus local Euler factor. -/
noncomputable def finiteSupportEulerFlux (a : Nat.Primes →₀ ℂ) (s : ℂ) : ℂ :=
  a.sum fun p c => localFluxJet (p : ℕ) c 0 s

/-- Pole-avoidance domain for a finite-support Euler parameter on `D`. -/
def IsFiniteSupportEulerFluxParameter (D : Set ℂ) (a : Nat.Primes →₀ ℂ) : Prop :=
  ∀ p ∈ a.support, ∀ s ∈ D, a p * ((p : ℕ) : ℂ) ^ (-s) ≠ 1

theorem finiteSupportEulerFlux_eq
    (a : Nat.Primes →₀ ℂ) (s : ℂ) :
    finiteSupportEulerFlux a s =
      a.sum fun p c =>
        (Real.log ((p : ℕ) : ℝ) : ℂ) * (c * ((p : ℕ) : ℂ) ^ (-s)) /
          (1 - c * ((p : ℕ) : ℂ) ^ (-s)) := by
  apply Finsupp.sum_congr
  intro p hp
  exact localFluxJet_zero_eq (p : ℕ) (a p) s

theorem differentiableOn_finiteSupportEulerFlux
    {D : Set ℂ} (a : Nat.Primes →₀ ℂ)
    (ha : IsFiniteSupportEulerFluxParameter D a) :
    DifferentiableOn ℂ (finiteSupportEulerFlux a) D := by
  intro s hs
  unfold finiteSupportEulerFlux
  apply DifferentiableWithinAt.fun_sum
  intro p hp
  exact (hasDerivAt_localFluxJet p.2.pos (a p) 0 (ha p hp s hs)).differentiableAt.differentiableWithinAt

/-- Actual finite Euler flux as a compact-open holomorphic function on its pole-free chart. -/
def finiteSupportEulerFluxOn
    (D : Set ℂ) (a : Nat.Primes →₀ ℂ)
    (ha : IsFiniteSupportEulerFluxParameter D a) : holoOn D :=
  ⟨⟨fun s => finiteSupportEulerFlux a (s : ℂ),
    (differentiableOn_finiteSupportEulerFlux a ha).continuousOn.restrict⟩,
    ⟨finiteSupportEulerFlux a, differentiableOn_finiteSupportEulerFlux a ha, fun _ => rfl⟩⟩

/-- Taylor coefficient of the actual nonlinear finite-prime Euler flux
`∑_p (log p) t a_p p^{-s} / (1 - t a_p p^{-s})`.  Degree one is its weighted tangent;
every higher degree is the exact `(log p) a_p^k p^{-ks}` coefficient. -/
def eulerFluxTaylorCoefficient (D : Set ℂ) (a : Nat.Primes →₀ ℂ) :
    ℕ → holoOn D
  | 0 => 0
  | 1 => primeEulerFluxTangentCoefficientMap D a
  | k + 2 => a.sum fun p c =>
      (((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * c ^ (k + 2)) •
        primePowerExponentialOn D p (k + 2)

@[simp] theorem eulerFluxTaylorCoefficient_zero
    (D : Set ℂ) (a : Nat.Primes →₀ ℂ) :
    eulerFluxTaylorCoefficient D a 0 = 0 := rfl

@[simp] theorem eulerFluxTaylorCoefficient_one
    (D : Set ℂ) (a : Nat.Primes →₀ ℂ) :
    eulerFluxTaylorCoefficient D a 1 = primeEulerFluxTangentCoefficientMap D a := rfl

/-- Local normal convergence of a continuous symmetric Taylor family on the compact-open space. -/
def HasCompactOpenNormalTaylorConvergence (D : Set ℂ)
    (B : ∀ n, symmetricContinuousMultilinearMapSubmodule (holoOn D) n) : Prop :=
  ∃ U : Set (holoOn D), U ∈ nhds 0 ∧
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ n, 0 ≤ M n) ∧
      ∀ n x, x ∈ U → ‖(B n).1 (fun _ => x)‖ ≤ M n

/-- Continuous analytic germ at zero, represented by a locally normally convergent family of
continuous symmetric homogeneous Taylor coefficients. -/
structure CompactOpenAnalyticGerm (D : Set ℂ) where
  coefficient : ∀ n, symmetricContinuousMultilinearMapSubmodule (holoOn D) n
  normalConvergence : HasCompactOpenNormalTaylorConvergence D coefficient

/-- Positive ordered compositions of total degree `n` into `m` source degrees. -/
def positiveOrderedCompositions (n m : ℕ) : Finset (Fin m → Fin (n + 1)) :=
  Finset.univ.filter fun d =>
    (∀ j, 0 < (d j : ℕ)) ∧ ∑ j, (d j : ℕ) = n

/-- Degree-`n` Taylor coefficient after pulling an analytic germ back through the actual
finite-prime Euler log-flux germ.  The degree-`n` all-linear contribution is separated from the
terms using lower germ degree and nonlinear prime-power source coefficients. -/
def eulerFluxCompositeTaylorCoefficient
    {D : Set ℂ} (g : CompactOpenAnalyticGerm D)
    (a : Nat.Primes →₀ ℂ) (n : ℕ) : ℂ :=
  (g.coefficient n).1 (fun _ => primeEulerFluxTangentCoefficientMap D a) +
    ∑ m ∈ Finset.range n,
      ∑ d ∈ positiveOrderedCompositions n m,
        (g.coefficient m).1 (fun j => eulerFluxTaylorCoefficient D a (d j : ℕ))

/-- Vanishing of the analytic germ on the nonlinear finite-support Euler log-flux microimage,
expressed intrinsically as vanishing of every coefficient of every pulled-back germ. -/
def CompactOpenAnalyticGerm.VanishesOnEulerFluxMicroimage
    {D : Set ℂ} (g : CompactOpenAnalyticGerm D) : Prop :=
  ∀ (a : Nat.Primes →₀ ℂ) (n : ℕ),
    eulerFluxCompositeTaylorCoefficient g a n = 0

/-- A continuous symmetric homogeneous coefficient that vanishes on the dense finite-prime
linear image vanishes identically. -/
theorem symmetricCoefficient_eq_zero_of_primeExponential_diagonal
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (n : ℕ)
    (B : symmetricContinuousMultilinearMapSubmodule (holoOn D) n)
    (hB : ∀ a : Nat.Primes →₀ ℂ,
      B.1 (fun _ => primeExponentialCoefficientMap D a) = 0) :
    B = 0 := by
  have hclosure := topologicalClosure_range_primeExponentialCoefficientMap_eq_top hDopen hDconv
  let Z : Set (holoOn D) := {x | B.1 (fun _ => x) = 0}
  have hdiagContinuous : Continuous (fun x : holoOn D => B.1 (fun _ => x)) := by
    exact B.1.cont.comp (continuous_pi fun _ => continuous_id)
  have hZclosed : IsClosed Z := isClosed_singleton.preimage hdiagContinuous
  have hrangeZ : (LinearMap.range (primeExponentialCoefficientMap D) : Set (holoOn D)) ⊆ Z := by
    rintro _ ⟨a, rfl⟩
    exact hB a
  have hclosureZ : closure (LinearMap.range (primeExponentialCoefficientMap D) :
      Set (holoOn D)) ⊆ Z := closure_minimal hrangeZ hZclosed
  apply (symmetricContinuousMultilinearMap_eq_zero_hasse_iff B).2
  intro x
  apply hclosureZ
  rw [← Submodule.topologicalClosure_coe, hclosure]
  trivial

/-- Weighted-tangent version used by the nonlinear Euler flux chart. -/
theorem symmetricCoefficient_eq_zero_of_primeEulerFluxTangent_diagonal
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (n : ℕ)
    (B : symmetricContinuousMultilinearMapSubmodule (holoOn D) n)
    (hB : ∀ a : Nat.Primes →₀ ℂ,
      B.1 (fun _ => primeEulerFluxTangentCoefficientMap D a) = 0) :
    B = 0 := by
  have hclosure :=
    topologicalClosure_range_primeEulerFluxTangentCoefficientMap_eq_top hDopen hDconv
  let Z : Set (holoOn D) := {x | B.1 (fun _ => x) = 0}
  have hdiagContinuous : Continuous (fun x : holoOn D => B.1 (fun _ => x)) := by
    exact B.1.cont.comp (continuous_pi fun _ => continuous_id)
  have hZclosed : IsClosed Z := isClosed_singleton.preimage hdiagContinuous
  have hrangeZ : (LinearMap.range (primeEulerFluxTangentCoefficientMap D) :
      Set (holoOn D)) ⊆ Z := by
    rintro _ ⟨a, rfl⟩
    exact hB a
  have hclosureZ : closure (LinearMap.range (primeEulerFluxTangentCoefficientMap D) :
      Set (holoOn D)) ⊆ Z := closure_minimal hrangeZ hZclosed
  apply (symmetricContinuousMultilinearMap_eq_zero_hasse_iff B).2
  intro x
  apply hclosureZ
  rw [← Submodule.topologicalClosure_coe, hclosure]
  trivial

/-- **Nonlinear determining-source theorem.**  On every convex domain, hence in particular every
bounded convex domain of the card, the finite-support Euler logarithmic flux microimage determines
every continuous analytic germ at zero. -/
theorem eulerFluxMicroimage_determines_compactOpenAnalyticGerm
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (_hDbounded : Bornology.IsBounded D) (_hDnonempty : D.Nonempty)
    (g : CompactOpenAnalyticGerm D)
    (hzero : g.VanishesOnEulerFluxMicroimage) :
    ∀ n, g.coefficient n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply symmetricCoefficient_eq_zero_of_primeEulerFluxTangent_diagonal hDopen hDconv
      intro a
      have hcomp := hzero a n
      rw [eulerFluxCompositeTaylorCoefficient] at hcomp
      have hlower :
          (∑ m ∈ Finset.range n,
            ∑ d ∈ positiveOrderedCompositions n m,
              (g.coefficient m).1
                (fun j => eulerFluxTaylorCoefficient D a (d j : ℕ))) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hm_lt : m < n := Finset.mem_range.mp hm
        rw [ih m hm_lt]
        simp
      rw [hlower, add_zero] at hcomp
      exact hcomp

/-- Germ at a fixed completed archimedean/boundary flux, written in increment coordinates. -/
abbrev CompactOpenAnalyticGermAt (D : Set ℂ) (_A : holoOn D) :=
  CompactOpenAnalyticGerm D

/-- Vanishing on `A + M` is the zero-centered Euler-flux pullback after translation by `A`. -/
def CompactOpenAnalyticGermAt.VanishesOnCompletedEulerFluxMicroimage
    {D : Set ℂ} {A : holoOn D} (g : CompactOpenAnalyticGermAt D A) : Prop :=
  g.VanishesOnEulerFluxMicroimage

/-- Adding a fixed archimedean/boundary flux is a translation and cannot create an analytic
equation on the completed finite-support Euler microimage. -/
theorem completedEulerFluxMicroimage_translation_determining
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (hDbounded : Bornology.IsBounded D) (hDnonempty : D.Nonempty)
    (A : holoOn D) (g : CompactOpenAnalyticGermAt D A)
    (hzero : g.VanishesOnCompletedEulerFluxMicroimage) :
    ∀ n, g.coefficient n = 0 :=
  eulerFluxMicroimage_determines_compactOpenAnalyticGerm
    hDopen hDconv hDbounded hDnonempty g hzero

end RHTower
