import GaloisForLFunctions.HTGeometry.BohrOrbitHaarLaw
import GaloisForLFunctions.HTGeometry.PairPhaseClock
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier
import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceIffUniformHeadTargetDensity

/-!
# Kronecker–Weyl limit law for the finite Euler product on a compact set

The finite Euler product `E_y(s) = ∏_{p ≤ y} (1 − p^{−s})^{−1}` at height `τ` is the phased product
`F_y(ω, z) = ∏_{p ≤ y} (1 − ω_p p^{−z})^{−1}` evaluated at the phases `ω_p = p^{−iτ}`
(`eulerPhaseProduct_circlePhaseFlow`).  The phases move along the flow of the frequencies `−log p`,
which are rationally independent, so by the Kronecker–Weyl theorem on the prime torus the time
averages of every continuous observable of the phases converge to its Haar integral
(`tendsto_windowAverage_primeFlow`).  Read on a compact `K ⊂ {Re z > 0}`, where `ω ↦ F_y(ω, ·)|_K`
is continuous into `C(K, ℂ)`, this is the limit law of the finite Euler product on `K`
(`tendsto_windowAverage_eulerProduct_functional`).

The visiting law follows: the flow spends in every open set of phases at least the proportion of
time given by its Haar measure (`eventually_ofReal_mul_le_volume_preimage_primeFlow`).  Hence if
one choice of phases brings `F_y(ω, ·)` within `ε` of a target `g` on `K`, the heights at which
`E_y(· + iτ)` is within `ε` of `g` on `K` have positive lower density
(`exists_pos_density_eulerTargetReturnSet`).  This is the first ingredient of universality; the
second, the existence of such phases for every nonvanishing target, is the Pechersky density lemma.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## The prime phase flow -/

/-- The frequency `−log p` of the phase `p^{−iτ}`. -/
def primeFrequency (p : Nat.Primes) : ℝ := -Real.log (p : ℕ)

/-- Negating every frequency preserves rational independence. -/
theorem rationallyIndependentSequence_neg {ι : Type*} {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) :
    RationallyIndependentSequence (fun i => -omega i) := by
  intro s n hn
  refine h s n ?_
  have hneg : finiteTorusCharacterDetuning n (fun i : (s : Set ι) => -omega i)
      = -finiteTorusCharacterDetuning n (fun i : (s : Set ι) => omega i) := by
    simp only [finiteTorusCharacterDetuning, mul_neg, Finset.sum_neg_distrib]
  rw [hneg] at hn
  exact neg_eq_zero.mp hn

/-- The frequencies `−log p` are rationally independent. -/
theorem rationallyIndependentSequence_primeFrequency :
    RationallyIndependentSequence primeFrequency :=
  rationallyIndependentSequence_neg
    (rationallyIndependentSequence_of_linearIndependent_int logPrime_linearIndependent_int)

/-- The circle phase flow of any frequency family is continuous in time. -/
theorem continuous_circlePhaseFlow {ι : Type*} (omega : ι → ℝ) :
    Continuous (circlePhaseFlow omega) := by
  have h : circlePhaseFlow omega
      = fun t => unitTorusHomeomorphCircles ι (clockPhasePoint omega t) :=
    funext fun t => circlePhaseFlow_eq omega t
  rw [h]
  exact (unitTorusHomeomorphCircles ι).continuous.comp (continuous_clockPhasePoint omega)

/-- **Kronecker–Weyl limit law along the prime phase flow.**  The time averages of a continuous
observable of the phases `(p^{−iτ})_p` converge to its Haar integral over the prime torus. -/
theorem tendsto_windowAverage_primeFlow (F : C((Nat.Primes → Circle), ℂ)) :
    Tendsto (windowAverage fun τ => F (circlePhaseFlow primeFrequency τ)) atTop
      (𝓝 (∫ x, F (unitTorusHomeomorphCircles Nat.Primes x) ∂(torusHaar Nat.Primes))) :=
  tendsto_windowAverage_haar_circlePhaseFlow rationallyIndependentSequence_primeFrequency F
    (F.continuous.comp (continuous_circlePhaseFlow _))
    (by simp only [sub_self]; exact tendsto_const_nhds)

/-- The real-valued form of the limit law. -/
theorem tendsto_windowAverage_primeFlow_real (ψ : C((Nat.Primes → Circle), ℝ)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ τ in (0 : ℝ)..T, ψ (circlePhaseFlow primeFrequency τ)) atTop
      (𝓝 (∫ x, ψ (unitTorusHomeomorphCircles Nat.Primes x) ∂(torusHaar Nat.Primes))) := by
  have h := tendsto_windowAverage_primeFlow
    ⟨fun ω => ((ψ ω : ℝ) : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
  have h2 := (Complex.continuous_re.tendsto _).comp h
  change Tendsto (fun T => (windowAverage
      (fun τ => ((ψ (circlePhaseFlow primeFrequency τ) : ℝ) : ℂ)) T).re) atTop
    (𝓝 ((∫ x, ((ψ (unitTorusHomeomorphCircles Nat.Primes x) : ℝ) : ℂ)
      ∂(torusHaar Nat.Primes)).re)) at h2
  have hlim : (∫ x, ((ψ (unitTorusHomeomorphCircles Nat.Primes x) : ℝ) : ℂ)
      ∂(torusHaar Nat.Primes)).re
      = ∫ x, ψ (unitTorusHomeomorphCircles Nat.Primes x) ∂(torusHaar Nat.Primes) := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hlim] at h2
  refine h2.congr' (Eventually.of_forall fun T => ?_)
  rw [windowAverage, intervalIntegral.integral_ofReal, Complex.real_smul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **Lower density of visits to an open set of phases.**  For an open set `U` of phases and any `c`
below the Haar measure of `U`, the prime phase flow spends at least the proportion `c` of every long
window `[0, T]` in `U`. -/
theorem eventually_ofReal_mul_le_volume_preimage_primeFlow {U : Set (Nat.Primes → Circle)}
    (hU : IsOpen U) {c : ℝ}
    (hc : c < (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U)).toReal) :
    ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Icc 0 T) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · filter_upwards [eventually_ge_atTop 0] with T hT
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc0 hT)]
    exact bot_le
  set V : Set (UnitAddTorus Nat.Primes) := unitTorusHomeomorphCircles Nat.Primes ⁻¹' U with hVdef
  have hV : IsOpen V := (Homeomorph.isOpen_preimage _).mpr hU
  -- inner regularity: a compact `C ⊆ V` carrying more than `c` of the Haar mass
  obtain ⟨C, hCV, hC, hcC⟩ : ∃ C, C ⊆ V ∧ IsCompact C ∧ c < (torusHaar Nat.Primes C).toReal := by
    have h1 : ENNReal.ofReal c < torusHaar Nat.Primes V :=
      (ENNReal.ofReal_lt_iff_lt_toReal hc0.le (measure_ne_top _ _)).mpr hc
    rw [hV.measure_eq_iSup_isCompact] at h1
    simp only [lt_iSup_iff] at h1
    obtain ⟨C, hCV, hC, hlt⟩ := h1
    exact ⟨C, hCV, hC, (ENNReal.ofReal_lt_iff_lt_toReal hc0.le (measure_ne_top _ _)).mp hlt⟩
  -- Urysohn: a continuous `f` with `1_C ≤ f ≤ 1_V`
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_compl_iff.mpr hV) hC.isClosed
    (Set.disjoint_left.mpr fun x hx hxC => hx (hCV hxC))
  have hint : c < ∫ x, f x ∂(torusHaar Nat.Primes) := by
    calc c < (torusHaar Nat.Primes C).toReal := hcC
      _ = ∫ x, C.indicator 1 x ∂(torusHaar Nat.Primes) := by
          rw [integral_indicator_one hC.measurableSet, measureReal_def]
      _ ≤ ∫ x, f x ∂(torusHaar Nat.Primes) := by
          refine integral_mono ((integrable_const (1 : ℝ)).indicator hC.measurableSet)
            (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            fun x => ?_
          by_cases hx : x ∈ C
          · rw [indicator_of_mem hx, Pi.one_apply]
            exact (hf1 hx).ge
          · rw [indicator_of_notMem hx]
            exact (hf01 x).1
  -- the observable on the phases
  let ψ : C((Nat.Primes → Circle), ℝ) :=
    f.comp ⟨(unitTorusHomeomorphCircles Nat.Primes).symm,
      (unitTorusHomeomorphCircles Nat.Primes).symm.continuous⟩
  have hψ : ∀ x, ψ (unitTorusHomeomorphCircles Nat.Primes x) = f x := fun x => by simp [ψ]
  have hL : ∫ x, ψ (unitTorusHomeomorphCircles Nat.Primes x) ∂(torusHaar Nat.Primes)
      = ∫ x, f x ∂(torusHaar Nat.Primes) := by simp only [hψ]
  have hT := tendsto_windowAverage_primeFlow_real ψ
  rw [hL] at hT
  have hS : MeasurableSet (circlePhaseFlow primeFrequency ⁻¹' U) :=
    (hU.preimage (continuous_circlePhaseFlow _)).measurableSet
  filter_upwards [hT.eventually_const_lt hint, eventually_gt_atTop 0] with T hlt hT0
  -- the time average of `ψ` along the flow is below the proportion of time spent in `U`
  have h1 : c * T < ∫ τ in (0 : ℝ)..T, ψ (circlePhaseFlow primeFrequency τ) := by
    have := mul_lt_mul_of_pos_right hlt hT0
    rwa [inv_mul_eq_div, div_mul_cancel₀ _ hT0.ne'] at this
  have hle : ∫ τ in (0 : ℝ)..T, ψ (circlePhaseFlow primeFrequency τ) ≤
      ∫ τ in (0 : ℝ)..T, (circlePhaseFlow primeFrequency ⁻¹' U).indicator (fun _ => (1 : ℝ)) τ := by
    refine intervalIntegral.integral_mono_on hT0.le
      ((ψ.continuous.comp (continuous_circlePhaseFlow _)).intervalIntegrable _ _) ?_
      fun τ _ => ?_
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le]
      exact (integrableOn_const (by simp) (by simp)).indicator hS
    · by_cases hτ : circlePhaseFlow primeFrequency τ ∈ U
      · rw [indicator_of_mem (show τ ∈ circlePhaseFlow primeFrequency ⁻¹' U from hτ)]
        exact (hf01 _).2
      · rw [indicator_of_notMem (show τ ∉ circlePhaseFlow primeFrequency ⁻¹' U from hτ)]
        have hV' : (unitTorusHomeomorphCircles Nat.Primes).symm (circlePhaseFlow primeFrequency τ)
            ∈ Vᶜ := by simpa [hVdef] using hτ
        exact (hf0 hV').le
  have h2 : ∫ τ in (0 : ℝ)..T,
      (circlePhaseFlow primeFrequency ⁻¹' U).indicator (fun _ => (1 : ℝ)) τ
      = (volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Ioc 0 T)).toReal := by
    rw [intervalIntegral.integral_of_le hT0.le, integral_indicator hS, setIntegral_const,
      measureReal_def, Measure.restrict_apply hS, smul_eq_mul, mul_one]
  have h3 : volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Ioc 0 T)
      ≤ volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Icc 0 T) :=
    measure_mono (inter_subset_inter_right _ Ioc_subset_Icc_self)
  refine ENNReal.ofReal_le_of_le_toReal ?_
  calc c * T ≤ (volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Ioc 0 T)).toReal := by
        linarith
    _ ≤ (volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Icc 0 T)).toReal :=
        ENNReal.toReal_mono
          ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne h3

/-- A nonempty open set of phases is visited with positive lower density. -/
theorem exists_pos_density_preimage_primeFlow {U : Set (Nat.Primes → Circle)} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (circlePhaseFlow primeFrequency ⁻¹' U ∩ Icc 0 T) := by
  have hV : IsOpen (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U) :=
    (Homeomorph.isOpen_preimage _).mpr hU
  have hVne : (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U).Nonempty := by
    obtain ⟨ω, hω⟩ := hne
    exact ⟨(unitTorusHomeomorphCircles Nat.Primes).symm ω, by simp [hω]⟩
  have hpos : 0 < (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹' U)).toReal :=
    ENNReal.toReal_pos (hV.measure_pos _ hVne).ne' (measure_ne_top _ _)
  exact ⟨_, half_pos hpos,
    eventually_ofReal_mul_le_volume_preimage_primeFlow hU (half_lt_self hpos)⟩

/-! ## The finite Euler product with phases -/

/-- The finite Euler product over the primes `≤ y`, with the unimodular phase `ω p` attached to the
prime `p`. -/
def eulerPhaseProduct (y : ℕ) (ω : Nat.Primes → Circle) (z : ℂ) : ℂ :=
  ∏ p ∈ primesLE y, (1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z))⁻¹

/-- With all phases equal to one this is the finite Euler product itself. -/
theorem eulerPhaseProduct_one (y : ℕ) (z : ℂ) :
    eulerPhaseProduct y 1 z = ∏ p ∈ primesLE y, (1 - ((p : ℕ) : ℂ) ^ (-z))⁻¹ := by
  simp [eulerPhaseProduct]

/-- `|p^{−z}| < 1` for `Re z > 0`. -/
theorem norm_prime_cpow_neg_lt_one_of_pos_re (p : Nat.Primes) {z : ℂ} (hz : 0 < z.re) :
    ‖((p : ℕ) : ℂ) ^ (-z)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)

/-- The Euler factors do not vanish for `Re z > 0`, whatever the phase. -/
theorem one_sub_phase_cpow_ne_zero (p : Nat.Primes) (w : Circle) {z : ℂ} (hz : 0 < z.re) :
    1 - (w : ℂ) * ((p : ℕ) : ℂ) ^ (-z) ≠ 0 := by
  intro h
  have h1 : (w : ℂ) * ((p : ℕ) : ℂ) ^ (-z) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, Circle.norm_coe, one_mul, norm_one] at h2
  exact (norm_prime_cpow_neg_lt_one_of_pos_re p hz).ne h2

/-- Joint continuity of the phased Euler product in the phases and in `z ∈ K ⊂ {Re z > 0}`. -/
theorem continuous_eulerPhaseProduct_prod (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re) :
    Continuous (fun q : (Nat.Primes → Circle) × K => eulerPhaseProduct y q.1 q.2) := by
  unfold eulerPhaseProduct
  refine continuous_finsetProd _ fun p _ => ?_
  refine Continuous.inv₀ ?_ fun q => one_sub_phase_cpow_ne_zero p (q.1 p) (hre q.2 q.2.2)
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  refine continuous_const.sub (Continuous.mul ?_ ?_)
  · exact continuous_subtype_val.comp ((continuous_apply p).comp continuous_fst)
  · exact (continuous_subtype_val.comp continuous_snd).neg.const_cpow (Or.inl hp0)

/-- Along the prime phase flow the phases are `p^{−iτ}`: the phased product at `z` is the plain
finite Euler product at `z + iτ`. -/
theorem eulerPhaseProduct_circlePhaseFlow (y : ℕ) (τ : ℝ) (z : ℂ) :
    eulerPhaseProduct y (circlePhaseFlow primeFrequency τ) z
      = eulerPhaseProduct y 1 (z + τ * I) := by
  unfold eulerPhaseProduct
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  rw [Pi.one_apply, Circle.coe_one, one_mul, circlePhaseFlow_coe]
  have hne : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_add,
    ← Complex.natCast_log]
  congr 1
  simp only [primeFrequency]
  push_cast
  ring

/-- For fixed phases the phased Euler product is continuous on `K ⊂ {Re z > 0}`. -/
theorem continuous_eulerPhaseProduct_section (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re)
    (ω : Nat.Primes → Circle) : Continuous fun z : K => eulerPhaseProduct y ω z := by
  have h := (continuous_eulerPhaseProduct_prod y hre).comp (Continuous.prodMk_right (Y := K) ω)
  exact h

/-- The phased Euler product restricted to a compact `K ⊂ {Re z > 0}`, as an element of
`C(K, ℂ)`. -/
def eulerPhaseProductOn (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re)
    (ω : Nat.Primes → Circle) : C(K, ℂ) :=
  ⟨fun z => eulerPhaseProduct y ω z, continuous_eulerPhaseProduct_section y hre ω⟩

theorem eulerPhaseProductOn_apply (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re)
    (ω : Nat.Primes → Circle) (z : K) :
    eulerPhaseProductOn y hre ω z = eulerPhaseProduct y ω z := rfl

/-- The phases enter continuously: `ω ↦ F_y(ω, ·)|_K` is continuous into `C(K, ℂ)`. -/
theorem continuous_eulerPhaseProductOn (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re) :
    Continuous (eulerPhaseProductOn y hre) := by
  refine ContinuousMap.continuous_of_continuous_uncurry (eulerPhaseProductOn y hre) ?_
  have h := continuous_eulerPhaseProduct_prod y hre
  exact h

theorem eulerPhaseProductOn_circlePhaseFlow_apply (y : ℕ) {K : Set ℂ} (hre : ∀ z ∈ K, 0 < z.re)
    (τ : ℝ) (z : K) :
    eulerPhaseProductOn y hre (circlePhaseFlow primeFrequency τ) z
      = eulerPhaseProduct y 1 (z + τ * I) :=
  eulerPhaseProduct_circlePhaseFlow y τ z

/-- **Limit law of the finite Euler product on `K`.**  For every continuous functional `Φ` on
`C(K, ℂ)`, the time averages of `Φ(E_y(· + iτ)|_K)` converge to the Haar integral of
`ω ↦ Φ(F_y(ω, ·)|_K)` over the prime torus. -/
theorem tendsto_windowAverage_eulerProduct_functional (y : ℕ) {K : Set ℂ}
    (hre : ∀ z ∈ K, 0 < z.re) (Φ : C(C(K, ℂ), ℂ)) :
    Tendsto (windowAverage fun τ =>
        Φ (eulerPhaseProductOn y hre (circlePhaseFlow primeFrequency τ))) atTop
      (𝓝 (∫ x, Φ (eulerPhaseProductOn y hre (unitTorusHomeomorphCircles Nat.Primes x))
        ∂(torusHaar Nat.Primes))) := by
  have h := tendsto_windowAverage_primeFlow
    (Φ.comp ⟨eulerPhaseProductOn y hre, continuous_eulerPhaseProductOn y hre⟩)
  exact h

/-! ## Visiting a target on `K` -/

/-- Phases at which the phased Euler product is within `ε` of the target `g` on `K`. -/
def eulerPhaseTargetSet (y : ℕ) (g : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set (Nat.Primes → Circle) :=
  {ω | ∀ z ∈ K, ‖eulerPhaseProduct y ω z - g z‖ < ε}

/-- For a compact `K ⊂ {Re z > 0}` and a target continuous on `K`, the set of approximating phases
is open. -/
theorem isOpen_eulerPhaseTargetSet (y : ℕ) {g : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hre : ∀ z ∈ K, 0 < z.re) (hg : ContinuousOn g K) (ε : ℝ) :
    IsOpen (eulerPhaseTargetSet y g K ε) := by
  rw [isOpen_iff_eventually]
  intro ω₀ hω₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hΦ : Continuous
      (fun q : (Nat.Primes → Circle) × K => ‖eulerPhaseProduct y q.1 q.2 - g q.2‖) :=
    ((continuous_eulerPhaseProduct_prod y hre).sub
      ((continuousOn_iff_continuous_restrict.mp hg).comp continuous_snd)).norm
  have h := (isCompact_univ (X := K)).eventually_forall_of_forall_eventually (x₀ := ω₀)
    (P := fun ω (z : K) => ‖eulerPhaseProduct y ω z - g z‖ < ε)
    (fun z _ => (hΦ.tendsto (ω₀, z)).eventually (eventually_lt_nhds (hω₀ z z.2)))
  exact h.mono fun ω hω z hz => hω ⟨z, hz⟩ (mem_univ _)

/-- Heights at which the finite Euler product is within `ε` of the target `g` on `K`. -/
def eulerTargetReturnSet (y : ℕ) (g : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ | ∀ z ∈ K, ‖eulerPhaseProduct y 1 (z + τ * I) - g z‖ < ε}

/-- The heights are exactly the times at which the prime phase flow lies in the approximating
phases. -/
theorem eulerTargetReturnSet_eq_preimage (y : ℕ) (g : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) :
    eulerTargetReturnSet y g K ε
      = circlePhaseFlow primeFrequency ⁻¹' eulerPhaseTargetSet y g K ε := by
  ext τ
  simp only [eulerTargetReturnSet, eulerPhaseTargetSet, mem_setOf_eq, mem_preimage,
    eulerPhaseProduct_circlePhaseFlow]

/-- **Quantitative visiting law.**  The lower density of the heights at which `E_y(· + iτ)` is within
`ε` of `g` on `K` is at least the Haar measure of the approximating phases. -/
theorem eventually_ofReal_mul_le_volume_eulerTargetReturnSet (y : ℕ) {g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hre : ∀ z ∈ K, 0 < z.re) (hg : ContinuousOn g K) {ε c : ℝ}
    (hc : c < (torusHaar Nat.Primes
      (unitTorusHomeomorphCircles Nat.Primes ⁻¹' eulerPhaseTargetSet y g K ε)).toReal) :
    ∀ᶠ T in atTop,
      ENNReal.ofReal (c * T) ≤ volume (eulerTargetReturnSet y g K ε ∩ Icc 0 T) := by
  rw [eulerTargetReturnSet_eq_preimage]
  exact eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_eulerPhaseTargetSet y hK hre hg ε) hc

/-- **Kronecker–Weyl visiting law on `K`.**  If some choice of phases brings the phased Euler product
within `ε` of `g` on the compact `K ⊂ {Re z > 0}`, then the heights at which the finite Euler
product itself is within `ε` of `g` on `K` have positive lower density. -/
theorem exists_pos_density_eulerTargetReturnSet (y : ℕ) {g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hre : ∀ z ∈ K, 0 < z.re) (hg : ContinuousOn g K) {ε : ℝ}
    (hω : ∃ ω : Nat.Primes → Circle, ∀ z ∈ K, ‖eulerPhaseProduct y ω z - g z‖ < ε) :
    ∃ c > 0, ∀ᶠ T in atTop,
      ENNReal.ofReal (c * T) ≤ volume (eulerTargetReturnSet y g K ε ∩ Icc 0 T) := by
  rw [eulerTargetReturnSet_eq_preimage]
  exact exists_pos_density_preimage_primeFlow (isOpen_eulerPhaseTargetSet y hK hre hg ε) hω

end RHTower
