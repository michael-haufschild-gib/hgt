import GaloisForLFunctions.HTGeometry.GaussianShiftInformation
import GaloisForLFunctions.HTGeometry.QuotientFusionProjectionGenesis

/-!
# Gaussian quotient--fusion capital

The formation-resource card `ULF-FRM-3`.

The corpus already owns the *scalar* quotient--fusion genesis
(`HTGeometry/QuotientFusionProjectionGenesis`).  What is new here is:

* §1  the genesis *signal vector* `g` of `(GQF.4)`, as the residual of the fused history against
  the fused range, with `‖g‖² = generatedEnergy` and the orthogonality `ℓ ⊥ g` of `(GQF.8)`;
* §2  `(GQF.9)` the exact inherited/genesis experiment factorization under `H = R ⊕ Rᗮ`,
  `(GQF.10)`–`(GQF.13)` the multiplicative affinity `exp(-(E_sep+Q)/8)`, `(GQF.11)` the two
  directed divergences `Q/2` and the Jeffreys work `Q`, `(GQF.12)` the Rényi capital
  `α(1-α)Q/2`;
* §3, §4  `(GQF.20)`, `(GQF.21)` exact depth `⌊b/Q⌋`, `(GQF.22)`, `(GQF.25)`, `(GQF.26)` cofinal
  properness and equalizer selection;
* §5  `(GQF.27)` the exact testing curve `Φ(-√(dQ)/2)` and `(GQF.28)` the testing exponent `Q/8`,
  via a Chernoff upper tail and an interval lower tail for the Gaussian;
* §6  `(GQF.30)`, `(GQF.31)` equivariance of the locally optimal history and invariance of the
  genesis energy under an equivariant orthogonal action.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Genesis

variable {ι : Type*} [Fintype ι] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K]
  {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, FiniteDimensional ℝ (H i)]

/-- The fused gauge map into the `ℓ²` direct sum. -/
def fusedMap (A : ∀ i, K →ₗ[ℝ] H i) : K →ₗ[ℝ] PiLp 2 H :=
  (WithLp.linearEquiv 2 ℝ (∀ i, H i)).symm.toLinearMap ∘ₗ LinearMap.pi A

@[simp] theorem fusedMap_ofLp (A : ∀ i, K →ₗ[ℝ] H i) (u : K) (i : ι) :
    (fusedMap A u).ofLp i = A i u := rfl

/-- `(GQF.8)` right factor: the fused range. -/
def fusedRange (A : ∀ i, K →ₗ[ℝ] H i) : Submodule ℝ (PiLp 2 H) := LinearMap.range (fusedMap A)

/-- The coordinatewise locally optimal history, as one vector of the fused space. -/
def historyVector (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : PiLp 2 H :=
  WithLp.toLp 2 fun i => localOptimalHistory A x i

@[simp] theorem historyVector_ofLp (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) :
    (historyVector A x).ofLp i = localOptimalHistory A x i := rfl

/-- `(GQF.2)`  The inherited residual `ℓ`. -/
def inheritedResidual (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : PiLp 2 H :=
  WithLp.toLp 2 fun i => x i - localOptimalHistory A x i

@[simp] theorem inheritedResidual_ofLp (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) :
    (inheritedResidual A x).ofLp i = x i - localOptimalHistory A x i := rfl

/-- `(GQF.4)`  The genesis signal `g`. -/
def genesisSignal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : PiLp 2 H :=
  historyVector A x - (fusedRange A).starProjection (historyVector A x)

theorem genesisSignal_mem_orthogonal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    genesisSignal A x ∈ (fusedRange A)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

theorem starProjection_le_of_mem (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i)
    {w : PiLp 2 H} (hw : w ∈ fusedRange A) :
    ‖genesisSignal A x‖ ≤ ‖historyVector A x - w‖ := by
  rw [genesisSignal, Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ (⟨w, hw⟩ : fusedRange A)

/-- `(GQF.5)`  `E_sep = ‖ℓ‖²`. -/
theorem norm_sq_inheritedResidual (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ‖inheritedResidual A x‖ ^ 2 = separateEnergy A x := by
  rw [PiLp.norm_sq_eq_of_L2, separateEnergy]
  exact Finset.sum_congr rfl fun i _ => by rw [inheritedResidual_ofLp]

/-- `(GQF.5)`  `Q = ‖g‖²` is the quotient--fusion genesis. -/
theorem norm_sq_genesisSignal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ‖genesisSignal A x‖ ^ 2 = generatedEnergy A x := by
  have hkey : ∀ u : K, ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2
      = ‖historyVector A x - fusedMap A u‖ ^ 2 := by
    intro u
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by
      congr 1
  obtain ⟨u₀, hu₀⟩ : ∃ u : K, fusedMap A u
      = (fusedRange A).starProjection (historyVector A x) :=
    Submodule.starProjection_apply_mem (fusedRange A) (historyVector A x)
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun u => ?_
    rw [hkey u]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (starProjection_le_of_mem A x (LinearMap.mem_range_self (fusedMap A) u)) 2
  · refine ciInf_le_of_le (bddBelow_generatedRange A x) u₀ ?_
    rw [hkey u₀, hu₀, ← genesisSignal]

theorem genesisSignal_ofLp_mem (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) :
    (genesisSignal A x).ofLp i ∈ LinearMap.range (A i) := by
  obtain ⟨u₀, hu₀⟩ : ∃ u : K, fusedMap A u
      = (fusedRange A).starProjection (historyVector A x) :=
    Submodule.starProjection_apply_mem (fusedRange A) (historyVector A x)
  have hcoord : (genesisSignal A x).ofLp i = localOptimalHistory A x i - A i u₀ := by
    rw [genesisSignal, ← hu₀]
    rfl
  rw [hcoord]
  exact Submodule.sub_mem _ (localOptimalHistory_mem A x i) (LinearMap.mem_range_self _ _)

/-- `(GQF.8)`  The inherited residual and the genesis signal are orthogonal. -/
theorem inner_inheritedResidual_genesisSignal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ⟪inheritedResidual A x, genesisSignal A x⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := (Submodule.sub_starProjection_mem_orthogonal
    (K := LinearMap.range (A i)) (x i)) _ (genesisSignal_ofLp_mem A x i)
  rw [inheritedResidual_ofLp, real_inner_comm]
  exact h

/-- Pythagoras for the inherited/genesis splitting. -/
theorem norm_sq_inheritedResidual_add_genesisSignal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ‖inheritedResidual A x + genesisSignal A x‖ ^ 2
      = separateEnergy A x + generatedEnergy A x := by
  rw [@norm_add_sq_real, inner_inheritedResidual_genesisSignal, norm_sq_inheritedResidual,
    norm_sq_genesisSignal]
  ring

/-- **`(GQF.6)`.**  The shared energy is the inherited energy plus the genesis energy. -/
theorem sharedEnergy_eq_norm_sq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    sharedEnergy A x = ‖inheritedResidual A x‖ ^ 2 + ‖genesisSignal A x‖ ^ 2 := by
  rw [norm_sq_inheritedResidual, norm_sq_genesisSignal]
  exact sharedEnergy_decomposition A x

/-- **`(GQF.6)` zero classification.** -/
theorem norm_genesisSignal_eq_zero_iff (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ‖genesisSignal A x‖ ^ 2 = 0 ↔ ∃ u : K, ∀ i, A i u = localOptimalHistory A x i := by
  rw [norm_sq_genesisSignal, ← quotientFusionGenesis_eq]
  exact quotientFusionGenesis_eq_zero_iff A x

end Genesis

/-! ## Capital of a Gaussian genesis packet -/

section Packet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian is reflection invariant. -/
theorem stdGaussian_map_neg : (stdGaussian E).map (fun x => -x) = stdGaussian E := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_stdGaussian]
  have hfun : ∀ x : E, Complex.exp ((⟪-x, t⟫ : ℝ) * Complex.I)
      = Complex.exp ((⟪x, -t⟫ : ℝ) * Complex.I) := by
    intro x
    rw [inner_neg_left, inner_neg_right]
  simp_rw [hfun]
  rw [← charFun_apply, charFun_stdGaussian, norm_neg]

/-- The two directed divergences of a Gaussian packet agree. -/
theorem klDiv_stdGaussian_shift_left (m : E) :
    klDiv (stdGaussian E) ((stdGaussian E).map (fun x => x + m))
      = ENNReal.ofReal (‖m‖ ^ 2 / 2) := by
  set T : E ≃ᵐ E := (Homeomorph.neg E).trans (Homeomorph.addRight m) |>.toMeasurableEquiv with hT
  have hTapp : ∀ x : E, T x = -x + m := fun x => rfl
  have hT₀ : (stdGaussian E).map T = (stdGaussian E).map (fun x => x + m) := by
    have h1 : (fun x : E => T x) = (fun y : E => y + m) ∘ (fun x : E => -x) := by
      funext x; rw [hTapp]; rfl
    rw [show ((T : E → E)) = (fun x : E => T x) from rfl, h1,
      ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_neg]
  have hT₁ : ((stdGaussian E).map (fun x => x + m)).map T = stdGaussian E := by
    have h1 : ((stdGaussian E).map (fun x => x + m)).map T
        = (stdGaussian E).map ((fun x : E => T x) ∘ (fun y : E => y + m)) := by
      rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    rw [h1]
    have h2 : ((fun x : E => T x) ∘ (fun y : E => y + m)) = (fun x : E => -x) := by
      funext x
      rw [Function.comp_apply, hTapp]
      abel
    rw [h2, stdGaussian_map_neg]
  calc klDiv (stdGaussian E) ((stdGaussian E).map (fun x => x + m))
      = klDiv ((stdGaussian E).map T) (((stdGaussian E).map (fun x => x + m)).map T) :=
        (klDiv_map_measurableEmbedding T.measurableEmbedding _ _).symm
    _ = klDiv ((stdGaussian E).map (fun x => x + m)) (stdGaussian E) := by rw [hT₀, hT₁]
    _ = ENNReal.ofReal (‖m‖ ^ 2 / 2) := klDiv_stdGaussian_shift m

/-- `(GQF.11)`  Jeffreys work of a Gaussian genesis packet. -/
theorem formationJeffreys_stdGaussian_shift (m : E) :
    formationJeffreys (stdGaussian E) ((stdGaussian E).map (fun x => x + m))
      = ENNReal.ofReal (‖m‖ ^ 2) := by
  rw [formationJeffreys, klDiv_stdGaussian_shift_left, klDiv_stdGaussian_shift,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- `(GQF.15)`  Rényi integral of a Gaussian genesis packet. -/
def gaussianRenyiIntegral (α : ℝ) (v : E) : ℝ≥0∞ :=
  ∫⁻ x, (((stdGaussian E).map (fun y => y + v)).rnDeriv (stdGaussian E) x) ^ (1 - α)
    ∂(stdGaussian E)

theorem gaussianRenyiIntegral_eq {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (v : E) :
    gaussianRenyiIntegral α v = ENNReal.ofReal (Real.exp (-(α * (1 - α) * ‖v‖ ^ 2 / 2))) := by
  rw [gaussianRenyiIntegral]
  rw [lintegral_congr_ae (by
    filter_upwards [rnDeriv_stdGaussian_shift v] with x hx
    rw [hx])]
  exact lintegral_cameronMartin_rpow hα0 hα1 v

/-- `(GQF.13)`  Bhattacharyya affinity of a Gaussian genesis packet. -/
theorem gaussianAffinity_eq (v : E) :
    gaussianRenyiIntegral (1 / 2) v = ENNReal.ofReal (Real.exp (-(‖v‖ ^ 2 / 8))) := by
  rw [gaussianRenyiIntegral_eq (by norm_num) (by norm_num)]
  congr 2
  ring

/-- `(GQF.12)`  Rényi capital of a Gaussian genesis packet. -/
def gaussianCapital (α : ℝ) (v : E) : ℝ := α * (1 - α) * ‖v‖ ^ 2 / 2

theorem gaussianRenyiIntegral_eq_exp_neg_capital {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (v : E) :
    gaussianRenyiIntegral α v = ENNReal.ofReal (Real.exp (-gaussianCapital α v)) := by
  rw [gaussianRenyiIntegral_eq hα0 hα1, gaussianCapital]

/-- `(GQF.11)`  Bhattacharyya formation capital. -/
theorem gaussianCapital_half (v : E) : gaussianCapital (1 / 2) v = ‖v‖ ^ 2 / 8 := by
  rw [gaussianCapital]
  ring

/-- **`(GQF.10)`.**  Orthogonal signals give an exactly multiplicative affinity. -/
theorem gaussianRenyiIntegral_orthogonal {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {u v : E}
    (h : ⟪u, v⟫ = 0) :
    gaussianRenyiIntegral α (u + v)
      = gaussianRenyiIntegral α u * gaussianRenyiIntegral α v := by
  rw [gaussianRenyiIntegral_eq hα0 hα1, gaussianRenyiIntegral_eq hα0 hα1,
    gaussianRenyiIntegral_eq hα0 hα1, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← Real.exp_add]
  congr 2
  rw [@norm_add_sq_real, h]
  ring

end Packet

/-! ## Exact formation depth and cofinal properness -/

/-- **`(GQF.21)`.**  The exact maximal independent genesis depth is `⌊b/Q⌋`. -/
theorem depth_le_floor_iff {b Q : ℝ} (hQ : 0 < Q) (hb : 0 ≤ b) (d : ℕ) :
    (d : ℝ) * Q ≤ b ↔ d ≤ ⌊b / Q⌋₊ := by
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hQ]

/-- **`(GQF.22)`.**  Cofinal genesis formation out of one finite budget forces neutral genesis. -/
theorem genesis_eq_zero_of_cofinal {b Q : ℝ} (hQ : 0 ≤ Q)
    (h : ∀ d : ℕ, ∃ d' : ℕ, d ≤ d' ∧ (d' : ℝ) * Q ≤ b) : Q = 0 := by
  by_contra hne
  have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hne)
  obtain ⟨d, hd⟩ := exists_nat_gt (b / Q)
  obtain ⟨d', hdd, hle⟩ := h d
  have : b / Q < (d' : ℝ) := lt_of_lt_of_le hd (by exact_mod_cast hdd)
  rw [div_lt_iff₀ hQpos] at this
  nlinarith

/-- **`(GQF.25)`, `(GQF.26)`.**  Fixed source plus cofinal source-coherent formation plus a trivial
synchronization equalizer force neutral displacement. -/
theorem displacement_eq_zero_of_cofinal {V : Type*} [Zero V] {Q : V → ℝ} {b : ℝ} {v : V}
    (hQ : ∀ w, 0 ≤ Q w) (hequal : ∀ w, Q w = 0 → w = 0)
    (h : ∀ d : ℕ, ∃ d' : ℕ, d ≤ d' ∧ (d' : ℝ) * Q v ≤ b) : v = 0 :=
  hequal v (genesis_eq_zero_of_cofinal (hQ v) h)

/-! ## The Gaussian tail and the exact testing exponent -/

/-- **Chernoff bound.**  `Φ(-t) ≤ exp(-t²/2)`. -/
theorem gaussianReal_Iic_neg_le {t : ℝ} (ht : 0 ≤ t) :
    gaussianReal 0 1 (Set.Iic (-t)) ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / 2))) := by
  have hbound : ∀ x : ℝ, (Set.Iic (-t)).indicator (fun _ => (1 : ℝ≥0∞)) x
      ≤ ENNReal.ofReal (Real.exp (x * (-t) - t ^ 2)) := by
    intro x
    by_cases hx : x ∈ Set.Iic (-t)
    · rw [Set.indicator_of_mem hx]
      have hxt : x ≤ -t := hx
      have : (0:ℝ) ≤ x * (-t) - t ^ 2 := by nlinarith
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by
        simpa using Real.one_le_exp this)
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  calc gaussianReal 0 1 (Set.Iic (-t))
      = ∫⁻ x, (Set.Iic (-t)).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(gaussianReal 0 1) := by
        rw [lintegral_indicator measurableSet_Iic]
        simp
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (x * (-t) - t ^ 2)) ∂(gaussianReal 0 1) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / 2))) := by
        have hsplit : ∀ x : ℝ, ENNReal.ofReal (Real.exp (x * (-t) - t ^ 2))
            = ENNReal.ofReal (Real.exp (-(t ^ 2))) * ENNReal.ofReal (Real.exp (x * (-t))) := by
          intro x
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          congr 2
          ring
        simp_rw [hsplit]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_mul_gaussianReal,
          ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring

/-- **Gaussian lower tail bound.**  `Φ(-t) ≥ exp(-(t+1)²/2)/√(2π)`. -/
theorem le_gaussianReal_Iic_neg {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-((t + 1) ^ 2 / 2)) / Real.sqrt (2 * Real.pi))
      ≤ gaussianReal 0 1 (Set.Iic (-t)) := by
  have hsub : Set.Icc (-t - 1) (-t) ⊆ Set.Iic (-t) := fun x hx => hx.2
  have hbound : ∀ x ∈ Set.Icc (-t - 1) (-t),
      ENNReal.ofReal (Real.exp (-((t + 1) ^ 2 / 2)) / Real.sqrt (2 * Real.pi))
        ≤ gaussianPDF 0 1 x := by
    intro x hx
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal]
    have hxx : x ^ 2 ≤ (t + 1) ^ 2 := by
      obtain ⟨h1, h2⟩ := hx
      nlinarith
    have hexp : Real.exp (-((t + 1) ^ 2 / 2))
        ≤ Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      push_cast
      nlinarith
    have hpi : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
      norm_num
    rw [hpi, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc ENNReal.ofReal (Real.exp (-((t + 1) ^ 2 / 2)) / Real.sqrt (2 * Real.pi))
      = ∫⁻ _ in Set.Icc (-t - 1) (-t),
          ENNReal.ofReal (Real.exp (-((t + 1) ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) := by
        rw [setLIntegral_const, Real.volume_Icc]
        have : (-t) - (-t - 1) = (1:ℝ) := by ring
        rw [this]
        simp
    _ ≤ ∫⁻ x in Set.Icc (-t - 1) (-t), gaussianPDF 0 1 x :=
        setLIntegral_mono (by fun_prop) hbound
    _ = gaussianReal 0 1 (Set.Icc (-t - 1) (-t)) := (gaussianReal_apply 0 one_ne_zero _).symm
    _ ≤ gaussianReal 0 1 (Set.Iic (-t)) := measure_mono hsub

theorem stdGaussianCDF_neg_le {t : ℝ} (ht : 0 ≤ t) :
    stdGaussianCDF (-t) ≤ Real.exp (-(t ^ 2 / 2)) := by
  have h := gaussianReal_Iic_neg_le ht
  have h' := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at h'
  exact h'

theorem le_stdGaussianCDF_neg {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((t + 1) ^ 2 / 2)) / Real.sqrt (2 * Real.pi) ≤ stdGaussianCDF (-t) := by
  have h := le_gaussianReal_Iic_neg ht
  have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  exact h'

theorem stdGaussianCDF_neg_pos {t : ℝ} (ht : 0 ≤ t) : 0 < stdGaussianCDF (-t) :=
  lt_of_lt_of_le (by positivity) (le_stdGaussianCDF_neg ht)

theorem sqrt_mul_div_self {Q : ℝ} (hQ : 0 ≤ Q) {d : ℝ} (hd : 0 < d) :
    Real.sqrt (d * Q) / d = Real.sqrt Q / Real.sqrt d := by
  rw [Real.sqrt_mul hd.le,
    div_eq_div_iff hd.ne' (Real.sqrt_ne_zero'.mpr hd)]
  linear_combination Real.sqrt Q * Real.mul_self_sqrt hd.le

/-- **Theorem 5.1, `(GQF.28)`.**  The Gaussian testing exponent of the independent genesis packet
is exactly the Bhattacharyya formation capital `Q/8`. -/
theorem tendsto_testing_exponent {Q : ℝ} (hQ : 0 < Q) :
    Filter.Tendsto
      (fun d : ℕ => -(1 / (d : ℝ)) * Real.log (stdGaussianCDF (-(Real.sqrt (d * Q) / 2))))
      Filter.atTop (nhds (Q / 8)) := by
  set C : ℝ := 1 / 2 + Real.log (Real.sqrt (2 * Real.pi)) with hC
  have hsq : ∀ d : ℕ, (Real.sqrt ((d : ℝ) * Q) / 2) ^ 2 = (d : ℝ) * Q / 4 := by
    intro d
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hnn : ∀ d : ℕ, (0:ℝ) ≤ Real.sqrt ((d : ℝ) * Q) / 2 := fun d => by positivity
  have hlow : ∀ d : ℕ, 1 ≤ d →
      Q / 8 ≤ -(1 / (d : ℝ)) * Real.log (stdGaussianCDF (-(Real.sqrt (d * Q) / 2))) := by
    intro d hd
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    have hpos := stdGaussianCDF_neg_pos (hnn d)
    have hlog : Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2)))
        ≤ -((d : ℝ) * Q / 8) := by
      have h1 : Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2)))
          ≤ Real.log (Real.exp (-((Real.sqrt ((d : ℝ) * Q) / 2) ^ 2 / 2))) :=
        Real.log_le_log hpos (stdGaussianCDF_neg_le (hnn d))
      rw [Real.log_exp, hsq d] at h1
      linarith
    have hstep : 0 ≤ (1 / (d:ℝ)) *
        (-(Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2)))) - (d : ℝ) * Q / 8) :=
      mul_nonneg (by positivity) (by linarith)
    have hexp : (1 / (d:ℝ)) *
        (-(Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2)))) - (d : ℝ) * Q / 8)
        = -(1 / (d : ℝ)) * Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2))) - Q / 8 := by
      field_simp
    linarith [hexp ▸ hstep]
  have hup : ∀ d : ℕ, 1 ≤ d →
      -(1 / (d : ℝ)) * Real.log (stdGaussianCDF (-(Real.sqrt (d * Q) / 2)))
        ≤ Q / 8 + (Real.sqrt Q / Real.sqrt (d : ℝ)) / 2 + C / (d : ℝ) := by
    intro d hd
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    have hlog : -((Real.sqrt ((d : ℝ) * Q) / 2 + 1) ^ 2 / 2) - Real.log (Real.sqrt (2 * Real.pi))
        ≤ Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2))) := by
      have h1 := Real.log_le_log
        (show (0:ℝ) < Real.exp (-((Real.sqrt ((d : ℝ) * Q) / 2 + 1) ^ 2 / 2))
          / Real.sqrt (2 * Real.pi) by positivity)
        (le_stdGaussianCDF_neg (hnn d))
      rwa [Real.log_div (by positivity) (by positivity), Real.log_exp] at h1
    have hexpand : (Real.sqrt ((d : ℝ) * Q) / 2 + 1) ^ 2
        = (d : ℝ) * Q / 4 + Real.sqrt ((d : ℝ) * Q) + 1 := by
      rw [add_sq, hsq d]
      ring
    rw [hexpand] at hlog
    have hbnd : -(Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2))))
        ≤ (d : ℝ) * Q / 8 + Real.sqrt ((d : ℝ) * Q) / 2 + C := by
      rw [hC]; linarith
    have hmul := mul_le_mul_of_nonneg_left hbnd
      (show (0:ℝ) ≤ 1 / (d:ℝ) by positivity)
    have heq1 : (1 / (d:ℝ)) * (-(Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2)))))
        = -(1 / (d : ℝ)) * Real.log (stdGaussianCDF (-(Real.sqrt ((d : ℝ) * Q) / 2))) := by ring
    have heq2 : (1 / (d:ℝ)) * ((d : ℝ) * Q / 8 + Real.sqrt ((d : ℝ) * Q) / 2 + C)
        = Q / 8 + (Real.sqrt ((d : ℝ) * Q) / (d:ℝ)) / 2 + C / (d:ℝ) := by
      field_simp
    rw [heq1, heq2, sqrt_mul_div_self hQ.le hdpos] at hmul
    exact hmul
  have hlim : Filter.Tendsto
      (fun d : ℕ => Q / 8 + (Real.sqrt Q / Real.sqrt (d : ℝ)) / 2 + C / (d : ℝ))
      Filter.atTop (nhds (Q / 8)) := by
    have ha : Filter.Tendsto (fun d : ℕ => (Real.sqrt (d : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hb : Filter.Tendsto (fun d : ℕ => ((d : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h1 : Filter.Tendsto (fun d : ℕ => (Real.sqrt Q / Real.sqrt (d : ℝ)) / 2)
        Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_comm, mul_assoc] using
        (ha.const_mul (Real.sqrt Q / 2))
    have h2 : Filter.Tendsto (fun d : ℕ => C / (d : ℝ)) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hb.const_mul C
    simpa using (tendsto_const_nhds.add h1).add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with d hd using hlow d hd
  · filter_upwards [Filter.eventually_ge_atTop 1] with d hd using hup d hd

/-! ## The genesis packet testing curve -/

section PacketCurve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Theorem 5.1, `(GQF.27)`.**  The exact equal-prior Bayes error of `d` independent genesis
packets. -/
theorem bayesError_genesisPacketPow (d : ℕ) (g : E) :
    bayesError (stdGaussian (PiLp 2 fun _ : Fin d => E))
        ((stdGaussian (PiLp 2 fun _ : Fin d => E)).map
          (fun y => y + (WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => E)))
      = stdGaussianCDF (-(Real.sqrt ((d : ℝ) * ‖g‖ ^ 2) / 2)) := by
  rw [bayesError_stdGaussian_shift]
  congr 2
  have h := norm_sq_packetPow (F := E) d g
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- **`(GQF.20)`.**  Exact independent genesis depth. -/
theorem nonempty_gaussianFormation_genesis_iff {b : ℝ} (hb : 0 < b) (d : ℕ) (g : E) :
    Nonempty (GaussianFormation b
        (WithLp.toLp 2 fun _ : Fin d => g : PiLp 2 fun _ : Fin d => E))
      ↔ (d : ℝ) * ‖g‖ ^ 2 ≤ b :=
  nonempty_gaussianFormation_packetPow_iff hb d g

end PacketCurve

/-! ## Functional-equation and recovery neutrality -/

section Equivariance

variable {ι : Type*} [Fintype ι] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K]
  {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, FiniteDimensional ℝ (H i)]

/-- An orthogonal isomorphism preserving a subspace commutes with the orthogonal projection onto
it. -/
theorem starProjection_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (W : Submodule ℝ F) (U : F ≃ₗᵢ[ℝ] F)
    (hUW : ∀ w ∈ W, U w ∈ W) (hUW' : ∀ w ∈ W, U.symm w ∈ W) (y : F) :
    W.starProjection (U y) = U (W.starProjection y) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hUW _ (W.starProjection_apply_mem y)) ?_
  intro w hw
  have hzero : ⟪y - W.starProjection y, U.symm w⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.sub_starProjection_mem_orthogonal y) _ (hUW' w hw)
  have hmap : U y - U (W.starProjection y) = U (y - W.starProjection y) := by
    rw [map_sub]
  rw [hmap]
  have := U.inner_map_map (y - W.starProjection y) (U.symm w)
  rw [U.apply_symm_apply] at this
  rw [this]
  exact hzero

/-- `(GQF.30)`  Equivariance of the locally optimal history. -/
theorem localOptimalHistory_equivariant (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i)
    (U : ∀ i, H i ≃ₗᵢ[ℝ] H i) (V : K ≃ₗᵢ[ℝ] K)
    (hUA : ∀ i u, U i (A i u) = A i (V u)) (i : ι) :
    localOptimalHistory A (fun j => U j (x j)) i = U i (localOptimalHistory A x i) := by
  have hinv : ∀ w ∈ LinearMap.range (A i), U i w ∈ LinearMap.range (A i) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨V u, (hUA i u).symm⟩
  have hinv' : ∀ w ∈ LinearMap.range (A i), (U i).symm w ∈ LinearMap.range (A i) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨V.symm u, ?_⟩
    have h := hUA i (V.symm u)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    rw [← h, LinearIsometryEquiv.symm_apply_apply]
  exact starProjection_linearIsometryEquiv _ (U i) hinv hinv' (x i)

/-- **`(GQF.31)`.**  The genesis energy is invariant under an equivariant orthogonal action. -/
theorem generatedEnergy_equivariant (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i)
    (U : ∀ i, H i ≃ₗᵢ[ℝ] H i) (V : K ≃ₗᵢ[ℝ] K)
    (hUA : ∀ i u, U i (A i u) = A i (V u)) :
    generatedEnergy A (fun j => U j (x j)) = generatedEnergy A x := by
  have hterm : ∀ (u : K) (i : ι),
      ‖localOptimalHistory A (fun j => U j (x j)) i - A i u‖
        = ‖localOptimalHistory A x i - A i (V.symm u)‖ := by
    intro u i
    rw [localOptimalHistory_equivariant A x U V hUA i]
    have h : A i u = U i (A i (V.symm u)) := by
      rw [hUA i (V.symm u), LinearIsometryEquiv.apply_symm_apply]
    rw [h, ← map_sub, LinearIsometryEquiv.norm_map]
  have hsets : (Set.range fun u : K => ∑ i, ‖localOptimalHistory A (fun j => U j (x j)) i
        - A i u‖ ^ 2)
      = Set.range fun u : K => ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2 := by
    ext r
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨V.symm u, (Finset.sum_congr rfl fun i _ => by rw [hterm u i]).symm⟩
    · rintro ⟨u, rfl⟩
      refine ⟨V u, Finset.sum_congr rfl fun i _ => ?_⟩
      rw [hterm (V u) i, LinearIsometryEquiv.symm_apply_apply]
  rw [generatedEnergy, generatedEnergy, iInf, iInf, hsets]

end Equivariance

/-! ## The exact inherited/genesis experiment factorization -/

section Factorization

variable {ι : Type*} [Fintype ι] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K]
  {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, FiniteDimensional ℝ (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

/-- `(GQF.8)` right factor: the coordinatewise range `R = ⊕ᵢ ran Aᵢ`. -/
def coordRange (A : ∀ i, K →ₗ[ℝ] H i) : Submodule ℝ (PiLp 2 H) where
  carrier := {v | ∀ i, v.ofLp i ∈ LinearMap.range (A i)}
  add_mem' := fun hv hw i => Submodule.add_mem _ (hv i) (hw i)
  zero_mem' := fun i => Submodule.zero_mem _
  smul_mem' := fun c _ hv i => Submodule.smul_mem _ c (hv i)

theorem mem_coordRange {A : ∀ i, K →ₗ[ℝ] H i} {v : PiLp 2 H} :
    v ∈ coordRange A ↔ ∀ i, v.ofLp i ∈ LinearMap.range (A i) := Iff.rfl

theorem genesisSignal_mem_coordRange (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    genesisSignal A x ∈ coordRange A := genesisSignal_ofLp_mem A x

theorem inheritedResidual_mem_orthogonal (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    inheritedResidual A x ∈ (coordRange A)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact (Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (A i)) (x i)) _ (hw i)

theorem starProjection_coordRange_split (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    (coordRange A).starProjection (inheritedResidual A x + genesisSignal A x)
      = genesisSignal A x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (genesisSignal_mem_coordRange A x) fun w hw => ?_
  have hsub : inheritedResidual A x + genesisSignal A x - genesisSignal A x
      = inheritedResidual A x := by abel
  rw [hsub, real_inner_comm]
  exact (Submodule.mem_orthogonal _ _).mp (inheritedResidual_mem_orthogonal A x) w hw

theorem starProjection_coordRange_orthogonal_split (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ((coordRange A)ᗮ).starProjection (inheritedResidual A x + genesisSignal A x)
      = inheritedResidual A x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (inheritedResidual_mem_orthogonal A x) fun w hw => ?_
  have hsub : inheritedResidual A x + genesisSignal A x - inheritedResidual A x
      = genesisSignal A x := by abel
  rw [hsub, real_inner_comm]
  exact (Submodule.mem_orthogonal _ _).mp
    (Submodule.le_orthogonal_orthogonal _ (genesisSignal_mem_coordRange A x)) w hw

/-- **Theorem 2.1, `(GQF.9)`.**  The Gaussian packet of `ℓ + g` factorizes, under the orthogonal
splitting `H = R ⊕ Rᗮ`, into the independent product of the genesis packet and the inherited
packet. -/
theorem gaussianPacket_factorization (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    (stdGaussian (PiLp 2 H)).map ((coordRange A).orthogonalDecomposition)
        = ((stdGaussian ↥(coordRange A)).prod
            (stdGaussian ↥((coordRange A)ᗮ))).map (WithLp.toLp 2) ∧
      ((stdGaussian (PiLp 2 H)).map
          (fun y => y + (inheritedResidual A x + genesisSignal A x))).map
          ((coordRange A).orthogonalDecomposition)
        = (((stdGaussian ↥(coordRange A)).map
              (fun y => y + (coordRange A).orthogonalProjectionOnto
                (inheritedResidual A x + genesisSignal A x))).prod
            ((stdGaussian ↥((coordRange A)ᗮ)).map
              (fun y => y + ((coordRange A)ᗮ).orthogonalProjectionOnto
                (inheritedResidual A x + genesisSignal A x)))).map (WithLp.toLp 2) := by
  set R := coordRange A with hR
  set T := R.orthogonalDecomposition with hT
  set v := inheritedResidual A x + genesisSignal A x with hv
  have hbase : (stdGaussian (PiLp 2 H)).map T
      = ((stdGaussian ↥R).prod (stdGaussian ↥Rᗮ)).map (WithLp.toLp 2) := by
    rw [hT, stdGaussian_map T, stdGaussian_prodL2]
  refine ⟨hbase, ?_⟩
  have hlin : ∀ y : PiLp 2 H, T (y + v) = T y + T v := fun y => by rw [map_add]
  have hstep : ((stdGaussian (PiLp 2 H)).map (fun y => y + v)).map T
      = ((stdGaussian (PiLp 2 H)).map T).map (fun z => z + T v) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext y
    simp only [Function.comp_apply]
    exact hlin y
  rw [hstep, hbase, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_apply]
  rw [Submodule.orthogonalDecomposition_apply]
  rfl

theorem coe_orthogonalProjectionOnto_genesis (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    (((coordRange A).orthogonalProjectionOnto
        (inheritedResidual A x + genesisSignal A x) : ↥(coordRange A)) : PiLp 2 H)
      = genesisSignal A x := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply, starProjection_coordRange_split]

theorem coe_orthogonalProjectionOnto_inherited (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ((((coordRange A)ᗮ).orthogonalProjectionOnto
        (inheritedResidual A x + genesisSignal A x) : ↥((coordRange A)ᗮ)) : PiLp 2 H)
      = inheritedResidual A x := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply, starProjection_coordRange_orthogonal_split]

/-- **`(GQF.10)`.**  The affinity of the fused packet is the product of the inherited and genesis
affinities, and equals `exp(-(E_sep + Q)/8)`. -/
theorem gaussianAffinity_fused (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    gaussianRenyiIntegral (1 / 2) (inheritedResidual A x + genesisSignal A x)
        = gaussianRenyiIntegral (1 / 2) (inheritedResidual A x)
          * gaussianRenyiIntegral (1 / 2) (genesisSignal A x) ∧
      gaussianRenyiIntegral (1 / 2) (inheritedResidual A x + genesisSignal A x)
        = ENNReal.ofReal
          (Real.exp (-((separateEnergy A x + generatedEnergy A x) / 8))) := by
  refine ⟨gaussianRenyiIntegral_orthogonal (by norm_num) (by norm_num)
    (inner_inheritedResidual_genesisSignal A x), ?_⟩
  rw [gaussianAffinity_eq, norm_sq_inheritedResidual_add_genesisSignal]

/-- The coordinatewise action of an orthogonal family on the fused space. -/
def fusedIsometry (U : ∀ i, H i ≃ₗᵢ[ℝ] H i) : PiLp 2 H ≃ₗᵢ[ℝ] PiLp 2 H :=
  LinearIsometryEquiv.piLpCongrRight 2 U

@[simp] theorem fusedIsometry_ofLp (U : ∀ i, H i ≃ₗᵢ[ℝ] H i) (v : PiLp 2 H) (i : ι) :
    (fusedIsometry U v).ofLp i = U i (v.ofLp i) := rfl

/-- **`(GQF.30)`.**  The genesis signal transforms equivariantly. -/
theorem genesisSignal_equivariant (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i)
    (U : ∀ i, H i ≃ₗᵢ[ℝ] H i) (V : K ≃ₗᵢ[ℝ] K)
    (hUA : ∀ i u, U i (A i u) = A i (V u)) :
    genesisSignal A (fun j => U j (x j)) = fusedIsometry U (genesisSignal A x) := by
  have hhist : historyVector A (fun j => U j (x j)) = fusedIsometry U (historyVector A x) := by
    refine PiLp.ext fun i => ?_
    rw [fusedIsometry_ofLp, historyVector_ofLp, historyVector_ofLp]
    exact localOptimalHistory_equivariant A x U V hUA i
  have hinv : ∀ w ∈ fusedRange A, fusedIsometry U w ∈ fusedRange A := by
    rintro _ ⟨u, rfl⟩
    refine ⟨V u, PiLp.ext fun i => ?_⟩
    rw [fusedMap_ofLp, fusedIsometry_ofLp, fusedMap_ofLp, hUA i u]
  have hinv' : ∀ w ∈ fusedRange A, (fusedIsometry U).symm w ∈ fusedRange A := by
    rintro _ ⟨u, rfl⟩
    refine ⟨V.symm u, PiLp.ext fun i => ?_⟩
    have hcoord : ((fusedIsometry U).symm (fusedMap A u)).ofLp i
        = (U i).symm ((fusedMap A u).ofLp i) := rfl
    rw [fusedMap_ofLp, hcoord, fusedMap_ofLp]
    have h := hUA i (V.symm u)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    rw [← h, LinearIsometryEquiv.symm_apply_apply]
  rw [genesisSignal, genesisSignal, hhist,
    starProjection_linearIsometryEquiv (fusedRange A) (fusedIsometry U) hinv hinv', ← map_sub]

/-- **`(GQF.32)`.**  An orthogonal isomorphism is an isomorphism of Gaussian packets. -/
theorem gaussianPacket_isometry_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (U : F ≃ₗᵢ[ℝ] F) (v : F) :
    (stdGaussian F).map U = stdGaussian F ∧
      ((stdGaussian F).map (fun y => y + v)).map U
        = (stdGaussian F).map (fun y => y + U v) := by
  refine ⟨stdGaussian_map U, ?_⟩
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun y : F => U y) ∘ (fun y : F => y + v) = (fun z : F => z + U v) ∘ (fun y : F => U y) := by
    funext y
    simp only [Function.comp_apply]
    rw [map_add]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map U]

end Factorization

end

end GaloisForLFunctions.HTGeometry
