import GaloisForLFunctions.HeckeLFunctions.HeckeThetaTailsDecayExponentially
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Mellin continuation of the actual Hecke theta pair

The physical and finite-Fourier dual theta sums are continuous for positive
Gaussian parameters. Their proved zero modes, exponential tails, and arithmetic
Poisson identity discharge every field of a Mellin functional-equation pair.
Its continued transforms have explicit residues at zero and the homogeneity
weight. Nonzero parity kills both poles. The exact affine Mellin-variable change
turns reflection about the weight into `s ↦ 1-s`.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory Set Filter Topology
open scoped Classical
open Asymptotics
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Archimedean place scaling depends continuously on its logarithmic profile. -/
theorem continuous_numberFieldPlaceScale_profile (z : mixedEmbedding.mixedSpace K) :
    Continuous (fun y : InfinitePlace K → ℝ => numberFieldMixedPlaceScale y z) := by
  change Continuous (fun y : InfinitePlace K → ℝ =>
    ((fun w : {w : InfinitePlace K // w.IsReal} => Real.exp (-y w.1) * z.1 w),
      fun w : {w : InfinitePlace K // w.IsComplex} => (Real.exp (-y w.1) : ℂ) * z.2 w))
  fun_prop

variable (𝔪 : Modulus K)

/-- A single arithmetic parity kernel is jointly continuous in profile and parameter. -/
theorem continuous_heckeParityKernel_parameters (ψ : HeckeCharacter 𝔪) (a : K) :
    Continuous (fun p : (InfinitePlace K → ℝ) × ℝ => heckeParityKernel 𝔪 ψ p.1 p.2 a) := by
  let x (p : (InfinitePlace K → ℝ) × ℝ) :=
    numberFieldTraceCoordinates (numberFieldMixedPlaceScale p.1 (mixedEmbedding K a))
  have hx : Continuous x := (numberFieldTraceCoordinates (K := K)).continuous.comp
    ((continuous_numberFieldPlaceScale_profile (mixedEmbedding K a)).comp continuous_fst)
  change Continuous (fun p => parityMonomial (heckeCoordinateParity 𝔪 ψ) (x p) *
    gaussianKernel (Real.pi * p.2) (x p))
  have hp : Continuous (fun p => parityMonomial (heckeCoordinateParity 𝔪 ψ) (x p)) := by
    unfold parityMonomial
    fun_prop
  have hg : Continuous (fun p => gaussianKernel (Real.pi * p.2) (x p)) := by
    unfold gaussianKernel
    fun_prop
  exact hp.mul hg

/-- The finite Hecke weight preserves joint continuity of each theta summand. -/
theorem continuous_heckeThetaKernel_parameters (ψ : HeckeCharacter 𝔪) (a : 𝓞 K) :
    Continuous (fun p : (InfinitePlace K → ℝ) × ℝ => heckeThetaKernel 𝔪 ψ p.1 p.2 a) :=
  continuous_const.mul (continuous_heckeParityKernel_parameters 𝔪 ψ (a : K))

/-- Increasing the positive Gaussian parameter decreases each parity-kernel norm. -/
theorem norm_parityGaussian_antitone_parameter {ι : Type*} [Fintype ι]
    (ε : ι → Bool) {a b : ℝ} (hab : a ≤ b) (x : EuclideanSpace ℝ ι) :
    ‖parityGaussian ε b x‖ ≤ ‖parityGaussian ε a x‖ := by
  simp only [parityGaussian, norm_mul, norm_gaussianKernel]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (sub_nonneg.mpr hab)
    (mul_nonneg Real.pi_pos.le (sq_nonneg ‖x‖))
  nlinarith only [h]

/-- The physical theta is continuous on positive parameters. -/
theorem continuousOn_heckeIdealTheta (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) : ContinuousOn (heckeIdealTheta 𝔪 ψ b y) (Ioi 0) := by
  intro t ht
  have hδ : 0 < t / 2 := half_pos ht
  have hcont : ContinuousOn (heckeIdealTheta 𝔪 ψ b y) (Ici (t / 2)) := by
    apply continuousOn_tsum
    · intro a
      exact ((continuous_heckeThetaKernel_parameters 𝔪 ψ (a : 𝓞 K)).comp
        (continuous_const.prodMk continuous_id)).continuousOn
    · exact summable_norm_heckeThetaKernel 𝔪 ψ b y hδ
    · intro a u hu
      change ‖integralHeckeWeight 𝔪 ψ (a : 𝓞 K) *
        parityGaussian (heckeCoordinateParity 𝔪 ψ) u _‖ ≤ _
      simp only [heckeThetaKernel, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_parityGaussian_antitone_parameter (heckeCoordinateParity 𝔪 ψ) hu _)
        (norm_nonneg _)
  exact (hcont.continuousAt (Ici_mem_nhds (half_lt_self ht))).continuousWithinAt

/-- The finite-Fourier dual theta is continuous on positive parameters. -/
theorem continuousOn_heckeDualIdealTheta {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) :
    ContinuousOn (heckeDualIdealTheta 𝔪 hb ψ y) (Ioi 0) := by
  intro t ht
  have hδ : 0 < t / 2 := half_pos ht
  have hcont : ContinuousOn (heckeDualIdealTheta 𝔪 hb ψ y) (Ici (t / 2)) := by
    apply continuousOn_tsum
    · intro a
      exact (continuous_const.mul ((continuous_heckeParityKernel_parameters 𝔪 ψ (a : K)).comp
        (continuous_const.prodMk continuous_id))).continuousOn
    · simpa only [neg_neg] using
        summable_norm_finiteHeckeFourierKernel 𝔪 hb ψ hb0 (-y) hδ
    · intro a u hu
      simp only [norm_mul, heckeParityKernel]
      exact mul_le_mul_of_nonneg_left
        (norm_parityGaussian_antitone_parameter (heckeCoordinateParity 𝔪 ψ) hu _)
        (norm_nonneg _)
  exact (hcont.continuousAt (Ici_mem_nhds (half_lt_self ht))).continuousWithinAt

/-- Physical theta has the local integrability required by its Mellin transform. -/
theorem locallyIntegrableOn_heckeIdealTheta (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) : LocallyIntegrableOn (heckeIdealTheta 𝔪 ψ b y) (Ioi 0) :=
  (continuousOn_heckeIdealTheta 𝔪 ψ b y).locallyIntegrableOn measurableSet_Ioi

/-- Dual theta has the local integrability required by its Mellin transform. -/
theorem locallyIntegrableOn_heckeDualIdealTheta {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) :
    LocallyIntegrableOn (heckeDualIdealTheta 𝔪 hb ψ y) (Ioi 0) :=
  (continuousOn_heckeDualIdealTheta 𝔪 hb hb0 ψ y).locallyIntegrableOn measurableSet_Ioi

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- The homogeneity exponent of the actual parity-weighted theta inversion. -/
def heckeThetaMellinWeight (ψ : HeckeCharacter 𝔪) : ℝ :=
  (Module.finrank ℚ K : ℝ) / 2 + parityDegree (heckeCoordinateParity 𝔪 ψ)

/-- The parameter-independent arithmetic scalar of theta inversion. -/
def heckeThetaMellinScalar (ψ : HeckeCharacter 𝔪) (I : FI)
    (y : InfinitePlace K → ℝ) : ℂ :=
  (Real.exp (∑ w : InfinitePlace K, (mult w : ℝ) * y w) : ℂ) *
    ((((FractionalIdeal.absNorm I : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
    (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)

/-- Positive field degree makes the theta Mellin weight positive. -/
theorem heckeThetaMellinWeight_pos (ψ : HeckeCharacter 𝔪) :
    0 < heckeThetaMellinWeight 𝔪 ψ := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  exact add_pos_of_pos_of_nonneg (half_pos hn) (Nat.cast_nonneg _)

/-- The arithmetic scalar cannot vanish for a nonzero ideal. -/
theorem heckeThetaMellinScalar_ne_zero (ψ : HeckeCharacter 𝔪) (I : FIˣ)
    (y : InfinitePlace K → ℝ) : heckeThetaMellinScalar 𝔪 ψ (I : FI) y ≠ 0 := by
  have hc : (FractionalIdeal.absNorm (I : FI) : ℝ) *
      Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by
    rw [← covolume_numberFieldTraceLattice]
    exact (ZLattice.covolume_pos (numberFieldTraceLattice I)).ne'
  exact mul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hc)))
    (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))

/-- At the reciprocal parameter, all scale powers combine into the Mellin weight. -/
theorem heckeThetaPoissonFactor_reciprocal (ψ : HeckeCharacter 𝔪) (I : FI)
    (y : InfinitePlace K → ℝ) {x : ℝ} (hx : 0 < x) :
    heckeThetaPoissonFactor 𝔪 ψ I y (1 / x) =
      heckeThetaMellinScalar 𝔪 ψ I y * (x ^ heckeThetaMellinWeight 𝔪 ψ : ℝ) := by
  unfold heckeThetaPoissonFactor heckeThetaMellinScalar heckeThetaMellinWeight
  rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv,
    Real.rpow_add hx, Real.rpow_natCast]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv,
    div_inv_eq_mul, mul_pow, Complex.ofReal_pow]
  ring

private theorem profile_le_abs_sum (y : InfinitePlace K → ℝ) (v : InfinitePlace K) :
    y v ≤ ∑ w, |y w| :=
  (le_abs_self _).trans (Finset.single_le_sum (fun w _ => abs_nonneg (y w)) (Finset.mem_univ v))

/-- The physical theta tail decreases faster than any real power. -/
theorem heckeIdealTheta_isBigO_rpow (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K))
    (y : InfinitePlace K → ℝ) (r : ℝ) :
    (fun t => heckeIdealTheta 𝔪 ψ b y t - heckeThetaConstant 𝔪 ψ) =O[atTop]
      (fun t : ℝ => t ^ r) := by
  obtain ⟨C, c, _, hc, hbound⟩ :=
    exists_uniform_exponential_heckeIdealTheta_tail 𝔪 ψ b (∑ v, |y v|)
  have hdecay : (fun t => heckeIdealTheta 𝔪 ψ b y t - heckeThetaConstant 𝔪 ψ) =O[atTop]
      (fun t : ℝ => Real.exp (-c * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using
      hbound y (profile_le_abs_sum y) t ht
  exact hdecay.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-- The actual finite-Fourier dual tail also decreases faster than every power. -/
theorem heckeDualIdealTheta_isBigO_rpow {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) (r : ℝ) :
    (fun t => heckeDualIdealTheta 𝔪 hb ψ y t - heckeDualThetaConstant 𝔪 ψ) =O[atTop]
      (fun t : ℝ => t ^ r) := by
  obtain ⟨C, c, _, hc, hbound⟩ :=
    exists_uniform_exponential_heckeDualIdealTheta_tail 𝔪 hb hb0 ψ (∑ v, |y v|)
  have hdecay : (fun t => heckeDualIdealTheta 𝔪 hb ψ y t - heckeDualThetaConstant 𝔪 ψ)
      =O[atTop] (fun t : ℝ => Real.exp (-c * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using
      hbound y (profile_le_abs_sum y) t ht
  exact hdecay.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-- Actual Hecke theta and its finite-Fourier dual satisfy every Mellin-pair hypothesis. -/
def heckeThetaMellinPair {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
    (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) : WeakFEPair ℂ where
  f := heckeIdealTheta 𝔪 ψ b y
  g := heckeDualIdealTheta 𝔪 hb ψ (-y)
  k := heckeThetaMellinWeight 𝔪 ψ
  ε := heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y
  f₀ := heckeThetaConstant 𝔪 ψ
  g₀ := heckeDualThetaConstant 𝔪 ψ
  hf_int := locallyIntegrableOn_heckeIdealTheta 𝔪 ψ b y
  hg_int := locallyIntegrableOn_heckeDualIdealTheta 𝔪 hb hb0 ψ (-y)
  hk := heckeThetaMellinWeight_pos 𝔪 ψ
  hε := by
    rw [← coe_idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)]
    exact heckeThetaMellinScalar_ne_zero 𝔪 ψ _ y
  h_feq := by
    intro x hx
    have h := heckeIdealTheta_poisson 𝔪 hb ψ hb0 y (one_div_pos.mpr hx)
    rw [heckeThetaPoissonFactor_reciprocal 𝔪 ψ _ y hx, one_div_one_div] at h
    exact h
  hf_top := heckeIdealTheta_isBigO_rpow 𝔪 ψ b y
  hg_top := heckeDualIdealTheta_isBigO_rpow 𝔪 hb hb0 ψ (-y)

variable {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)

/-- The entire part obtained by subtracting the actual theta zero modes. -/
def heckeThetaMellinRegularPart (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) : ℂ → ℂ :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).Λ₀

/-- The continued Mellin transform of physical theta minus its zero mode. -/
def heckeThetaMellinContinuation (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ) : ℂ → ℂ :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).Λ

/-- The continued Mellin transform of the finite-Fourier dual at the opposite profile. -/
def heckeDualThetaMellinContinuation (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) : ℂ → ℂ :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).symm.Λ

/-- Subtracting the two explicit polar terms leaves an entire function. -/
theorem differentiable_heckeThetaMellinRegularPart (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) : Differentiable ℂ (heckeThetaMellinRegularPart 𝔪 hb hb0 ψ y) :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).differentiable_Λ₀

/-- The only possible singularities are zero and the theta homogeneity weight. -/
theorem differentiableAt_heckeThetaMellinContinuation (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {s : ℂ} (hs : s ≠ 0)
    (hsk : s ≠ (heckeThetaMellinWeight 𝔪 ψ : ℂ)) :
    DifferentiableAt ℂ (heckeThetaMellinContinuation 𝔪 hb hb0 ψ y) s :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).differentiableAt_Λ (Or.inl hs) (Or.inl hsk)

/-- The continued expression agrees with the convergent physical theta Mellin integral. -/
theorem hasMellin_heckeIdealTheta (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {s : ℂ} (hs : heckeThetaMellinWeight 𝔪 ψ < s.re) :
    HasMellin (fun t => heckeIdealTheta 𝔪 ψ b y t - heckeThetaConstant 𝔪 ψ) s
      (heckeThetaMellinContinuation 𝔪 hb hb0 ψ y s) :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).hasMellin hs

/-- The symmetric continuation agrees with the actual finite-Fourier dual integral. -/
theorem hasMellin_heckeDualIdealTheta (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {s : ℂ} (hs : heckeThetaMellinWeight 𝔪 ψ < s.re) :
    HasMellin (fun t => heckeDualIdealTheta 𝔪 hb ψ (-y) t - heckeDualThetaConstant 𝔪 ψ) s
      (heckeDualThetaMellinContinuation 𝔪 hb hb0 ψ y s) :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).symm.hasMellin hs

/-- The actual continued theta Mellin pair satisfies its arithmetic functional equation. -/
theorem heckeThetaMellinContinuation_functional_equation (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (s : ℂ) :
    heckeThetaMellinContinuation 𝔪 hb hb0 ψ y (heckeThetaMellinWeight 𝔪 ψ - s) =
      heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y *
        heckeDualThetaMellinContinuation 𝔪 hb hb0 ψ y s :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).functional_equation s

/-- The residue at zero is the negative physical zero term. -/
theorem heckeThetaMellinContinuation_residue_zero (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) :
    Tendsto (fun s : ℂ => s * heckeThetaMellinContinuation 𝔪 hb hb0 ψ y s)
      (𝓝[≠] 0) (𝓝 (-heckeThetaConstant 𝔪 ψ)) :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).Λ_residue_zero

/-- The residue at the weight is the arithmetic scalar times the dual zero term. -/
theorem heckeThetaMellinContinuation_residue_weight (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) :
    Tendsto (fun s : ℂ => (s - heckeThetaMellinWeight 𝔪 ψ) *
      heckeThetaMellinContinuation 𝔪 hb hb0 ψ y s)
      (𝓝[≠] (heckeThetaMellinWeight 𝔪 ψ : ℂ))
      (𝓝 (heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y *
        heckeDualThetaConstant 𝔪 ψ)) :=
  (heckeThetaMellinPair 𝔪 hb hb0 ψ y).Λ_residue_k

/-- A nonzero parity kills both actual zero modes. -/
theorem heckeThetaMellinPair_isStrong_of_parity_ne_zero (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (h : parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    IsStrongFEPair (heckeThetaMellinPair 𝔪 hb hb0 ψ y) := by
  constructor
  · change heckeThetaConstant 𝔪 ψ = 0
    simp only [heckeThetaConstant, h, and_false, if_false]
  · change heckeDualThetaConstant 𝔪 ψ = 0
    simp only [heckeDualThetaConstant, h, false_and, if_false]

/-- Nonzero parity makes the actual theta Mellin continuation entire. -/
theorem differentiable_heckeThetaMellinContinuation_of_parity_ne_zero (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (h : parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    Differentiable ℂ (heckeThetaMellinContinuation 𝔪 hb hb0 ψ y) :=
  (heckeThetaMellinPair_isStrong_of_parity_ne_zero 𝔪 hb hb0 ψ y h).differentiable_Λ

/-- The affine change of Mellin variable corresponding to the Hecke variable. -/
def heckeThetaMellinArgument (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  ((Module.finrank ℚ K : ℂ) * s + parityDegree (heckeCoordinateParity 𝔪 ψ)) / 2

/-- The theta weight becomes the symmetry `s ↦ 1-s` in the Hecke variable. -/
theorem heckeThetaMellinArgument_one_sub (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeThetaMellinArgument 𝔪 ψ (1 - s) =
      heckeThetaMellinWeight 𝔪 ψ - heckeThetaMellinArgument 𝔪 ψ s := by
  simp only [heckeThetaMellinArgument, heckeThetaMellinWeight, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

/-- The continued theta transform has the standard reflection after the exact variable change. -/
theorem heckeThetaMellinContinuation_reflection (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (s : ℂ) :
    heckeThetaMellinContinuation 𝔪 hb hb0 ψ y (heckeThetaMellinArgument 𝔪 ψ (1 - s)) =
      heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) y *
        heckeDualThetaMellinContinuation 𝔪 hb hb0 ψ y (heckeThetaMellinArgument 𝔪 ψ s) := by
  rw [heckeThetaMellinArgument_one_sub]
  exact heckeThetaMellinContinuation_functional_equation 𝔪 hb hb0 ψ y _

end GaloisForLFunctions.HeckeLFunctions
