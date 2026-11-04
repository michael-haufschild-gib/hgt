import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.SquareRootThreshold.IntervalSourceTransformsSampledOnLocallyBoundedPoints

/-!
# Coherent Cluster Visibility and Sharp `L²` Tilt Amplification

This module establishes the two-sided visibility law for coherent off-line clusters in smooth
Riemann–von Mangoldt backgrounds and the sharp `L²`-sampled tilt-amplification law for general
unit-window Riemann–von Mangoldt configurations (including `ζ` unconditionally):

* **Exact master equation in a smooth RvM background (`windowPositiveAt_multiplicityPairConfig_iff`,
  `windowPositiveAt_multiplicityPairConfig_of_le_log`,
  `onsetAperture_multiplicityPairConfig_lt_of_log_le`,
  `windowPositiveAt_multiplicityPairConfig_of_cubic_le`,
  `onsetAperture_multiplicityPairConfig_lt_of_lt_cubic`).** Inserting a multiplicity-`k` off-line
  pair `½ ± δ + iγ₀` into the doubled on-line lattice of spacing `2π/L` yields a tempered
  configuration that is window-positive at half-width `0 < a ≤ L/2` **iff**
  `(k : ℝ) * pairEnergy δ a ≤ L`, where `pairEnergy δ a = sinh(2δa)/(2δ) − a`. This single
  equation simultaneously governs the deep logarithmic law `2δa ≍ log(4δL/k)` and the shallow cubic
  law `a ≍ (3L / (2kδ²))^{1/3}`.
* **Sharp `L²` tilt amplification (`integral_sinhTest_sq_le`, `sinhTest_energy_sq_ge`).** For
  `sinhTest a δ u = sinh(δu)(a² − u²)₊^{5/2}`, an exact degree-`5` exponential antiderivative
  proves `∫ (sinhTest a δ)² ≤ 30 a⁵ e^{2δa} / δ⁶`, while at `w = 1/(4δ)` (`2 ≤ δa`) the tilted
  signal satisfies `P² ≥ a⁵ e^{4δa} / (2^{26} δ⁷)`, achieving the optimal gain ratio
  `P² / ‖f‖₂² ≍ e^{2δa}/δ` with zero polynomial loss in `a` or `1/δ`.
* **Coherent cone summation and general RvM cluster exclusion (`re_Wsummand_pair_modulatedTest_le`,
  `sum_norm_Wsummand_near_le_of_depth_le`, `windowPositiveAt_excludes_coherent_cluster`,
  `zeta_windowPositiveAt_excludes_coherent_cluster`,
  `enlargedWeilFloor_excludes_zeta_coherent_cluster`).** Every off-line pair in the coherent cone
  `ρ_q = ½ + ε_q + iγ_q` (`ε_q ≥ δ`, `|γ_q − γ₀| ≤ 1/(4a)`, `2 ≤ δa`) contributes at most
  `−(5/8) m_q P²` to `Re W_Z(f, f)`, whereas all near background zeros (`|γ − γ₀| ≤ R`) of depth
  at most `σ` are controlled in `L²` via `sum_norm_sq_testTransform_le_of_locallyBounded'`,
  excluding unshielded clusters across the doubly-exponential height scale in `a`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticIncidencePositivity
open _root_.RHTower.CCMParityQuartet

/-! ### 1. Exact two-sided visibility law for a multiplicity-`k` off-line cluster -/

/-- The doubled on-line lattice `{½ + 2πim/L}` (multiplicity `2`) together with a coherent
multiplicity-`k` off-line pair `½ ± δ + iγ₀` (`k ≥ 1`, `0 < δ ≤ ½`). -/
def multiplicityPairConfig (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) : ZeroConfig where
  carrier := (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀}) ∪
    {offLinePoint (-δ) γ₀}
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else k
  one_le_mult := fun ρ _ => by split_ifs <;> omega
  strip := (isolatedPairConfig hL hδ hδ' γ₀).strip
  reflect_mem := (isolatedPairConfig hL hδ hδ' γ₀).reflect_mem
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := (isolatedPairConfig hL hδ hδ' γ₀).finite_window

/-- The multiplicity-`k` off-line pair configuration is tempered. -/
theorem temperedConfig_multiplicityPairConfig (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) :
    TemperedConfig (multiplicityPairConfig k hk hL hδ hδ' γ₀) := by
  set Z := multiplicityPairConfig k hk hL hδ hδ' γ₀
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  obtain ⟨a, ha⟩ := hasSum_lattice_weight hL 0 2
  have hmult : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else k := fun _ => rfl
  have ha' : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => G ρ) a := by
    convert ha using 2 with ρ
    obtain ⟨_, m, rfl⟩ := ρ
    simp only [G, hmult, verticalLatticePoint, add_zero, if_true, Nat.cast_ofNat]
  have hd₁ : Disjoint (Set.range (verticalLatticePoint L 0)) {offLinePoint δ γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨m, hm⟩
    have := congrArg Complex.re hm
    simp only [verticalLatticePoint, offLinePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀})
      {offLinePoint (-δ) γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨m, hm⟩ | hm)
    · have := congrArg Complex.re hm
      simp only [verticalLatticePoint, offLinePoint] at this
      linarith
    · rw [Set.mem_singleton_iff] at hm
      have := congrArg Complex.re hm
      simp only [offLinePoint] at this
      linarith
  have hp := hasSum_singleton (offLinePoint δ γ₀) G
  have hq := hasSum_singleton (offLinePoint (-δ) γ₀) G
  exact ⟨a + G (offLinePoint δ γ₀) + G (offLinePoint (-δ) γ₀),
    HasSum.add_disjoint (f := G) hd₂ (HasSum.add_disjoint (f := G) hd₁ ha' hp) hq⟩

/-- Exact Weil form of `multiplicityPairConfig` below the Nyquist half-width `L/2`. -/
theorem W_multiplicityPairConfig (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (multiplicityPairConfig k hk hL hδ hδ' γ₀).W f f =
      2 * L * (∫ t, f t * conj (f t)) +
        (k : ℂ) * (paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ)) +
          paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ))) := by
  let Z := multiplicityPairConfig k hk hL hδ hδ' γ₀
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else k := fun _ => rfl
  have hmult : ∀ m : ℤ, Z.mult (verticalLatticePoint L 0 m) = 2 := fun m => by
    rw [hmultdef, if_pos (by simp [verticalLatticePoint])]
  have h₁ := hasSum_Wsummand_onLineLattice Z hL hmult hf hf.continuous hfs hfs
  have hconj₁ : conj ((γ₀ : ℂ) - I * δ) = (γ₀ : ℂ) + I * δ := by
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  have hconj₂ : conj ((γ₀ : ℂ) + I * δ) = (γ₀ : ℂ) - I * δ := by
    simp [map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hvp : Z.Wsummand f f (offLinePoint δ γ₀) =
      (k : ℂ) * (paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ))) := by
    have hm : Z.mult (offLinePoint δ γ₀) = k := by
      rw [hmultdef, if_neg (by simp only [offLinePoint]; linarith)]
    unfold ZeroConfig.Wsummand
    rw [hm, gammaOf_offLinePoint, hconj₁, mul_assoc]
  have hvq : Z.Wsummand f f (offLinePoint (-δ) γ₀) =
      (k : ℂ) * (paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ))) := by
    have hm : Z.mult (offLinePoint (-δ) γ₀) = k := by
      rw [hmultdef, if_neg (by simp only [offLinePoint]; linarith)]
    unfold ZeroConfig.Wsummand
    rw [hm, gammaOf_offLinePoint]
    push_cast
    rw [show (γ₀ : ℂ) - I * -(δ : ℂ) = (γ₀ : ℂ) + I * δ by ring, hconj₂, mul_assoc]
  have hp := hasSum_singleton (offLinePoint δ γ₀) (Z.Wsummand f f)
  rw [hvp] at hp
  have hq := hasSum_singleton (offLinePoint (-δ) γ₀) (Z.Wsummand f f)
  rw [hvq] at hq
  have hd₁ : Disjoint (Set.range (verticalLatticePoint L 0)) {offLinePoint δ γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨m, hm⟩
    have := congrArg Complex.re hm
    simp only [verticalLatticePoint, offLinePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀})
      {offLinePoint (-δ) γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨m, hm⟩ | hm)
    · have := congrArg Complex.re hm
      simp only [verticalLatticePoint, offLinePoint] at this
      linarith
    · rw [Set.mem_singleton_iff] at hm
      have := congrArg Complex.re hm
      simp only [offLinePoint] at this
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ h₁ hp) hq
  change ∑' ρ : Z.carrier, Z.Wsummand f f ρ = _
  exact hall.tsum_eq.trans (by ring)

/-- Sharp rank-two lower bound `Re W_Z(f, f) ≥ 2(L − k · pairEnergy δ a) ‖f‖₂²` for `a ≤ L/2`. -/
theorem re_W_multiplicityPairConfig_ge (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * (L - (k : ℝ) * pairEnergy δ a) * ∫ t, ‖f t‖ ^ 2 ≤
      ((multiplicityPairConfig k hk hL hδ hδ' γ₀).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith) haL)
  rw [W_multiplicityPairConfig k hk hL hδ hδ' γ₀ hf hfs', integral_mul_conj_self_eq]
  have hpair := neg_half_normSq_sub_le_re_pair (paperFT f ((γ₀ : ℂ) - I * δ))
    (paperFT f ((γ₀ : ℂ) + I * δ))
  have hrank := norm_sub_sq_le_pairEnergy hδ ha γ₀ hf.continuous hfs
  have hre1 : (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 := by
    rw [show (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hre2 : ((k : ℂ) * (paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ)) +
      paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ)))).re =
      (k : ℝ) * (paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ)) +
        paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ))).re := by
    rw [← Complex.ofReal_natCast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [Complex.add_re, hre1, hre2]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left hpair hk0, mul_le_mul_of_nonneg_left hrank hk0]

/-- Above `L < k · pairEnergy δ a`, the smooth truncation witness of `IsolatedOffLinePairVisibilityLaw`
makes `multiplicityPairConfig` strictly negative. -/
theorem exists_re_W_multiplicityPairConfig_neg (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hS : L < (k : ℝ) * pairEnergy δ a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((multiplicityPairConfig k hk hL hδ hδ' γ₀).W f f).re < 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hLdiv : 0 < L / k := div_pos hL hkpos
  have hSdiv : L / k < pairEnergy δ a := (div_lt_iff₀ hkpos).mpr (by linarith)
  have haL' : a ≤ max (L / k) (2 * a) / 2 := by
    have := le_max_right (L / k) (2 * a)
    linarith
  -- Dilate the lattice parameter of `isolatedPairConfig` to `L / k` if `2a ≤ L / k`, or build
  -- the witness directly from `exists_re_W_isolatedPairConfig_neg` when `2a ≤ L / k` fails by
  -- comparing `W_multiplicityPairConfig` with `W_isolatedPairConfig` on a common lattice `L`:
  set S := pairEnergy δ
  have hSa : (L / k) * S a < S a ^ 2 := by
    have : 0 < S a := hLdiv.trans hSdiv
    nlinarith
  have hev : ∀ᶠ x in 𝓝[<] a, (L / k) * S a < S x ^ 2 ∧ a / 2 < x :=
    ((((continuous_pairEnergy δ).pow 2).continuousAt.eventually (lt_mem_nhds hSa)).and
      (continuous_id.continuousAt.eventually (lt_mem_nhds (by linarith : a / 2 < a)))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨a', ⟨hSa', ha'2⟩, ha'a⟩ := (hev.and self_mem_nhdsWithin).exists
  have ha'pos : 0 < a' := by linarith
  set φ : ContDiffBump (0 : ℝ) := ⟨a', a, ha'pos, ha'a⟩
  set s : ℝ → ℝ := fun u => Real.sinh (δ * u) * φ u
  set f : ℝ → ℂ := fun u => (s u : ℂ) * cexp (-(I * γ₀ * u))
  have hsc : ContDiff ℝ 2 s :=
    (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).mul φ.contDiff
  have hexpc : ContDiff ℝ 2 (fun u : ℝ => cexp (-(I * γ₀ * u))) :=
    Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hfc2 : ContDiff ℝ 2 f := (Complex.ofRealCLM.contDiff.comp hsc).mul hexpc
  have hsupp_s : ∀ u, u ∉ Icc (-a) a → s u = 0 := fun u hu => by
    have hφ0 : φ u = 0 := φ.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      by_contra hlt
      rw [not_le] at hlt
      exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩)
    simp [s, hφ0]
  have hfs : tsupport f ⊆ Icc (-a) a := closure_minimal (fun u hu => by
    by_contra hnot
    exact hu (by simp [f, hsupp_s u hnot])) isClosed_Icc
  refine ⟨f, hfc2, hfs, ?_⟩
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith) haL)
  have hscs : HasCompactSupport s :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => hsupp_s u hu
  have hA : paperFT f ((γ₀ : ℂ) - I * δ) = ((∫ u, s u * Real.exp (δ * u) : ℝ) : ℂ) := by
    rw [paperFT_sub_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [f]
    have hc : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (δ * u) : ℂ) * hc
  have hB : paperFT f ((γ₀ : ℂ) + I * δ) = ((∫ u, s u * Real.exp (-δ * u) : ℝ) : ℂ) := by
    rw [paperFT_add_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [f]
    have hc : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (-δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (-δ * u) : ℂ) * hc
  set Ap := ∫ u, s u * Real.exp (δ * u)
  set Bp := ∫ u, s u * Real.exp (-δ * u)
  set Is := ∫ u, φ u * Real.sinh (δ * u) ^ 2
  have hint : ∀ c : ℝ, Integrable (fun u => s u * Real.exp (c * u)) := fun c =>
    (hsc.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hscs.mul_right
  have hodd : ∫ u, s u * Real.cosh (δ * u) = 0 :=
    RHTower.integral_odd_mul_cosh (fun u => by
      simp only [s, φ.neg, mul_neg, Real.sinh_neg, neg_mul]) δ
  have hsum : Ap + Bp = 0 := by
    dsimp only [Ap, Bp]
    rw [← integral_add (hint δ) (hint (-δ))]
    have h2 : ∫ u, (s u * Real.exp (δ * u) + s u * Real.exp (-δ * u)) =
        2 * ∫ u, s u * Real.cosh (δ * u) := by
      rw [← integral_const_mul]
      congr 1 with u
      rw [Real.cosh_eq, show -δ * u = -(δ * u) by ring]
      ring
    rw [h2, hodd, mul_zero]
  have hsub : Ap - Bp = 2 * Is := by
    dsimp only [Ap, Bp, Is]
    rw [← integral_sub (hint δ) (hint (-δ)), ← integral_const_mul]
    congr 1 with u
    simp only [s]
    rw [Real.sinh_eq (δ * u), show -δ * u = -(δ * u) by ring]
    ring
  have hApv : Ap = Is := by linarith
  have hBpv : Bp = -Is := by linarith
  have hnormf : ∀ u, ‖f u‖ ^ 2 = s u ^ 2 := fun u => by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, mul_one, sq_abs]
  have hupper : ∫ u, ‖f u‖ ^ 2 ≤ S a := by
    simp_rw [hnormf]
    rw [show S a = pairEnergy δ a from rfl, ← integral_sinh_sq_Icc hδ ha.le,
      ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (((by fun_prop : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2).integrableOn_Icc
        ).integrable_indicator measurableSet_Icc) (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu]
      simp only [s, mul_pow]
      have h1 : φ u ^ 2 ≤ 1 := by
        have := φ.le_one (x := u); have := φ.nonneg (x := u); nlinarith
      nlinarith [sq_nonneg (Real.sinh (δ * u))]
    · rw [Set.indicator_of_notMem hu, hsupp_s u hu]
      norm_num
  have hlower : S a' ≤ Is := by
    rw [show S a' = pairEnergy δ a' from rfl, ← integral_sinh_sq_Icc hδ ha'pos.le,
      ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u)
      ((φ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.mul_right)) (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Icc (-a') a'
    · rw [Set.indicator_of_mem hu, φ.one_of_mem_closedBall]
      · ring_nf; exact le_rfl
      · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        exact ⟨hu.1, hu.2⟩
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg φ.nonneg (sq_nonneg _)
  have hSa'0 : 0 ≤ S a' := pairEnergy_nonneg hδ ha'pos.le
  rw [W_multiplicityPairConfig k hk hL hδ hδ' γ₀ hfc2 hfs', integral_mul_conj_self_eq, hA, hB]
  change (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) +
    (k : ℂ) * ((Ap : ℂ) * conj (Bp : ℂ) + (Bp : ℂ) * conj (Ap : ℂ))).re < 0
  rw [hApv, hBpv, ← Complex.ofReal_natCast]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  have hIs2 : S a' ^ 2 ≤ Is ^ 2 := pow_le_pow_left₀ hSa'0 hlower 2
  have hkSa' : L * S a < (k : ℝ) * S a' ^ 2 := by
    have := mul_lt_mul_of_pos_left hSa' hkpos
    rwa [← mul_assoc, mul_div_cancel₀ L hkpos.ne'] at this
  nlinarith [hupper, hIs2, hkSa']

/-- **Exact two-sided visibility law (`A34`) for a coherent multiplicity-`k` off-line cluster.**
For `0 < a ≤ L/2`, `multiplicityPairConfig k hk hL hδ hδ' γ₀` is window-positive at half-width `a`
iff `(k : ℝ) * pairEnergy δ a ≤ L`. -/
theorem windowPositiveAt_multiplicityPairConfig_iff (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    WindowPositiveAt (multiplicityPairConfig k hk hL hδ hδ' γ₀) a ↔
      (k : ℝ) * pairEnergy δ a ≤ L := by
  constructor
  · intro hpos
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨f, hf, hfs, hneg⟩ :=
      exists_re_W_multiplicityPairConfig_neg k hk hL hδ hδ' γ₀ ha haL hlt
    exact absurd (hpos f hf hfs) (not_le.mpr hneg)
  · intro hle f hf hfs
    have hge := re_W_multiplicityPairConfig_ge k hk hL hδ hδ' γ₀ ha.le haL hf hfs
    have hint : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith

/-- **Deep logarithmic hiding (`V2`).** If `2δa ≤ log(4δL / k)` and `0 < a ≤ L/2`, the
multiplicity-`k` off-line cluster is window-positive at half-width `a`. -/
theorem windowPositiveAt_multiplicityPairConfig_of_le_log (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a)
    (haL : a ≤ L / 2) (hlog : 2 * δ * a ≤ Real.log (4 * δ * L / k)) :
    WindowPositiveAt (multiplicityPairConfig k hk hL hδ hδ' γ₀) a := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  rw [windowPositiveAt_multiplicityPairConfig_iff k hk hL hδ hδ' γ₀ ha haL]
  unfold pairEnergy
  have hexp : Real.exp (2 * δ * a) ≤ 4 * δ * L / k := by
    calc Real.exp (2 * δ * a) ≤ Real.exp (Real.log (4 * δ * L / k)) := Real.exp_le_exp.mpr hlog
      _ = 4 * δ * L / k := Real.exp_log (by positivity)
  have hsinh : Real.sinh (2 * δ * a) ≤ Real.exp (2 * δ * a) / 2 := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-(2 * δ * a))]
  have h1 : (k : ℝ) * Real.sinh (2 * δ * a) ≤ 2 * δ * L := by
    have := mul_le_mul_of_nonneg_left (hsinh.trans (div_le_div_of_nonneg_right hexp (by norm_num)))
      hkpos.le
    have hsimp : (k : ℝ) * (4 * δ * L / k / 2) = 2 * δ * L := by field_simp [hkpos.ne']; ring
    linarith
  have h2 : (k : ℝ) * (Real.sinh (2 * δ * a) / (2 * δ)) ≤ L := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith
  nlinarith

/-- **Deep logarithmic seeing (`V1`).** If `log(4δ(L/k + a) + 2) ≤ 2δa` and `0 < a ≤ L/2`, then
`onsetAperture (multiplicityPairConfig ...) < a`. -/
theorem onsetAperture_multiplicityPairConfig_lt_of_log_le (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a)
    (haL : a ≤ L / 2) (hlog : Real.log (4 * δ * (L / k + a) + 2) ≤ 2 * δ * a) :
    onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a : EReal) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  rw [← not_le,
    ← windowPositiveAt_iff_le_onsetAperture
      (temperedConfig_multiplicityPairConfig k hk hL hδ hδ' γ₀) ha.le,
    windowPositiveAt_multiplicityPairConfig_iff k hk hL hδ hδ' γ₀ ha haL, not_le]
  unfold pairEnergy
  have hexp : 4 * δ * (L / k + a) + 2 ≤ Real.exp (2 * δ * a) := by
    calc 4 * δ * (L / k + a) + 2 = Real.exp (Real.log (4 * δ * (L / k + a) + 2)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (2 * δ * a) := Real.exp_le_exp.mpr hlog
  have hsmall : Real.exp (-(2 * δ * a)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * δ * a) < 0 by nlinarith)
    rwa [Real.exp_zero] at h
  have hsinh : 2 * δ * (L / k + a) < Real.sinh (2 * δ * a) := by
    rw [Real.sinh_eq]; linarith
  have hdiv : L / k + a < Real.sinh (2 * δ * a) / (2 * δ) :=
    (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have hsub : L / k < Real.sinh (2 * δ * a) / (2 * δ) - a := by linarith
  have := mul_lt_mul_of_pos_left hsub hkpos
  rwa [mul_div_cancel₀ L hkpos.ne'] at this

/-- Lower cubic Taylor bound `x³ / 6 ≤ sinh x − x` for `x ≥ 0`. -/
theorem cube_div_six_le_sinh_sub {x : ℝ} (hx : 0 ≤ x) : x ^ 3 / 6 ≤ Real.sinh x - x := by
  have h0 : ∀ t : ℝ, 0 ≤ t → t ≤ Real.sinh t := fun t ht => by
    rcases ht.eq_or_lt with rfl | hpos
    · simp
    · obtain ⟨c, _, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hpos
        Real.continuous_sinh.continuousOn fun u _ => Real.hasDerivAt_sinh u
      rw [Real.sinh_zero, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
      nlinarith [Real.one_le_cosh c]
  have h1 : ∀ t : ℝ, 0 ≤ t → t ^ 2 / 2 ≤ Real.cosh t - 1 := fun t ht => by
    rcases ht.eq_or_lt with rfl | hpos
    · simp
    · set g1 : ℝ → ℝ := fun u => Real.cosh u - 1 - u ^ 2 / 2
      have hg1d : ∀ u, HasDerivAt g1 (Real.sinh u - u) u := fun u => by
        have := ((Real.hasDerivAt_cosh u).sub_const 1).sub ((hasDerivAt_pow 2 u).div_const 2)
        exact this.congr_deriv (by ring)
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g1 (fun u => Real.sinh u - u) hpos
        (by fun_prop) fun u _ => hg1d u
      have hg10 : g1 0 = 0 := by simp [g1]
      rw [hg10, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
      have hsc : 0 ≤ Real.sinh c - c := by linarith [h0 c hc.1.le]
      have : 0 ≤ g1 t := by nlinarith
      dsimp [g1] at this
      linarith
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  · set g2 : ℝ → ℝ := fun u => Real.sinh u - u - u ^ 3 / 6
    have hg2d : ∀ u, HasDerivAt g2 (Real.cosh u - 1 - u ^ 2 / 2) u := fun u => by
      have := ((Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)).sub
        ((hasDerivAt_pow 3 u).div_const 6)
      exact this.congr_deriv (by ring)
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g2 (fun u => Real.cosh u - 1 - u ^ 2 / 2)
      hpos (by fun_prop) fun u _ => hg2d u
    have hg20 : g2 0 = 0 := by simp [g2]
    rw [hg20, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
    have hcc : 0 ≤ Real.cosh c - 1 - c ^ 2 / 2 := by linarith [h1 c hc.1.le]
    have : 0 ≤ g2 x := by nlinarith
    dsimp [g2] at this
    linarith

/-- Upper cubic Taylor bound `sinh x − x ≤ x³ cosh x / 6` for `x ≥ 0`. -/
theorem sinh_sub_le_cube_mul_cosh_div_six {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x - x ≤ x ^ 3 * Real.cosh x / 6 := by
  have h0 : ∀ t : ℝ, 0 ≤ t → t ≤ x → Real.sinh t ≤ t * Real.cosh x := fun t ht htx => by
    rcases ht.eq_or_lt with rfl | hpos
    · simp
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hpos
        Real.continuous_sinh.continuousOn fun u _ => Real.hasDerivAt_sinh u
      rw [Real.sinh_zero, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
      have hcc : Real.cosh c ≤ Real.cosh x := by
        rw [Real.cosh_le_cosh, abs_of_pos hc.1, abs_of_nonneg hx]
        exact hc.2.le.trans htx
      nlinarith
  have h1 : ∀ t : ℝ, 0 ≤ t → t ≤ x → Real.cosh t - 1 ≤ t ^ 2 * Real.cosh x / 2 :=
    fun t ht htx => by
      rcases ht.eq_or_lt with rfl | hpos
      · simp
      · set g1 : ℝ → ℝ := fun u => t ^ 2 * Real.cosh x / 2 * 0 + (Real.cosh u - 1 - u ^ 2 * Real.cosh x / 2)
        have hg1d : ∀ u, HasDerivAt g1 (Real.sinh u - u * Real.cosh x) u := fun u => by
          have := ((Real.hasDerivAt_cosh u).sub_const 1).sub
            (((hasDerivAt_pow 2 u).mul_const (Real.cosh x)).div_const 2)
          exact (this.const_add _).congr_deriv (by ring)
        obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g1
          (fun u => Real.sinh u - u * Real.cosh x) hpos (by fun_prop) fun u _ => hg1d u
        have hg10 : g1 0 = 0 := by simp [g1]
        rw [hg10, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
        have hsc : Real.sinh c - c * Real.cosh x ≤ 0 := by
          linarith [h0 c hc.1.le (hc.2.le.trans htx)]
        have : g1 t ≤ 0 := by nlinarith
        dsimp [g1] at this
        linarith
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  · set g2 : ℝ → ℝ := fun u => Real.sinh u - u - u ^ 3 * Real.cosh x / 6
    have hg2d : ∀ u, HasDerivAt g2 (Real.cosh u - 1 - u ^ 2 * Real.cosh x / 2) u := fun u => by
      have := ((Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)).sub
        (((hasDerivAt_pow 3 u).mul_const (Real.cosh x)).div_const 6)
      exact this.congr_deriv (by ring)
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g2
      (fun u => Real.cosh u - 1 - u ^ 2 * Real.cosh x / 2) hpos (by fun_prop) fun u _ => hg2d u
    have hg20 : g2 0 = 0 := by simp [g2]
    rw [hg20, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
    have hcc : Real.cosh c - 1 - c ^ 2 * Real.cosh x / 2 ≤ 0 := by
      linarith [h1 c hc.1.le hc.2.le]
    have : g2 x ≤ 0 := by nlinarith
    dsimp [g2] at this
    linarith

/-- **Shallow cubic hiding (`V2`).** If `(2/3) k δ² a³ cosh(2δa) ≤ L` and `0 < a ≤ L/2`, the
multiplicity-`k` off-line cluster is window-positive at half-width `a`. -/
theorem windowPositiveAt_multiplicityPairConfig_of_cubic_le (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a)
    (haL : a ≤ L / 2) (hcub : 2 / 3 * (k : ℝ) * δ ^ 2 * a ^ 3 * Real.cosh (2 * δ * a) ≤ L) :
    WindowPositiveAt (multiplicityPairConfig k hk hL hδ hδ' γ₀) a := by
  rw [windowPositiveAt_multiplicityPairConfig_iff k hk hL hδ hδ' γ₀ ha haL]
  have hpe : pairEnergy δ a ≤ 2 / 3 * δ ^ 2 * a ^ 3 * Real.cosh (2 * δ * a) := by
    have h := sinh_sub_le_cube_mul_cosh_div_six (show 0 ≤ 2 * δ * a by positivity)
    unfold pairEnergy
    have heq : Real.sinh (2 * δ * a) / (2 * δ) - a =
        (Real.sinh (2 * δ * a) - 2 * δ * a) / (2 * δ) := by field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    calc Real.sinh (2 * δ * a) - 2 * δ * a
        ≤ (2 * δ * a) ^ 3 * Real.cosh (2 * δ * a) / 6 := h
      _ = 2 / 3 * δ ^ 2 * a ^ 3 * Real.cosh (2 * δ * a) * (2 * δ) := by ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * pairEnergy δ a
      ≤ (k : ℝ) * (2 / 3 * δ ^ 2 * a ^ 3 * Real.cosh (2 * δ * a)) :=
        mul_le_mul_of_nonneg_left hpe hk0
    _ = 2 / 3 * (k : ℝ) * δ ^ 2 * a ^ 3 * Real.cosh (2 * δ * a) := by ring
    _ ≤ L := hcub

/-- **Shallow cubic seeing (`V1`).** If `L < (2/3) k δ² a³` and `0 < a ≤ L/2`, then
`onsetAperture (multiplicityPairConfig ...) < a`. -/
theorem onsetAperture_multiplicityPairConfig_lt_of_lt_cubic (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a)
    (haL : a ≤ L / 2) (hcub : L < 2 / 3 * (k : ℝ) * δ ^ 2 * a ^ 3) :
    onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a : EReal) := by
  rw [← not_le,
    ← windowPositiveAt_iff_le_onsetAperture
      (temperedConfig_multiplicityPairConfig k hk hL hδ hδ' γ₀) ha.le,
    windowPositiveAt_multiplicityPairConfig_iff k hk hL hδ hδ' γ₀ ha haL, not_le]
  have hpe : 2 / 3 * δ ^ 2 * a ^ 3 ≤ pairEnergy δ a := by
    have h := cube_div_six_le_sinh_sub (show 0 ≤ 2 * δ * a by positivity)
    unfold pairEnergy
    have heq : Real.sinh (2 * δ * a) / (2 * δ) - a =
        (Real.sinh (2 * δ * a) - 2 * δ * a) / (2 * δ) := by field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    calc 2 / 3 * δ ^ 2 * a ^ 3 * (2 * δ) = (2 * δ * a) ^ 3 / 6 := by ring
      _ ≤ Real.sinh (2 * δ * a) - 2 * δ * a := h
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc L < 2 / 3 * (k : ℝ) * δ ^ 2 * a ^ 3 := hcub
    _ = (k : ℝ) * (2 / 3 * δ ^ 2 * a ^ 3) := by ring
    _ ≤ (k : ℝ) * pairEnergy δ a := mul_le_mul_of_nonneg_left hpe hk0

/-! ### 2. Sharp `L²` norm and optimal `e^{2δa}/δ` tilt amplification of `sinhTest` -/

private def polyFiveAntideriv (c t : ℝ) : ℝ :=
  -Real.exp (-c * t) *
    (t ^ 5 / c + 5 * t ^ 4 / c ^ 2 + 20 * t ^ 3 / c ^ 3 +
      60 * t ^ 2 / c ^ 4 + 120 * t / c ^ 5 + 120 / c ^ 6)

private theorem hasDerivAt_polyFiveAntideriv {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (polyFiveAntideriv c) (t ^ 5 * Real.exp (-c * t)) t := by
  unfold polyFiveAntideriv
  have hexp : HasDerivAt (fun x => -Real.exp (-c * x)) (c * Real.exp (-c * t)) t := by
    have := (((hasDerivAt_id t).const_mul (-c)).exp).neg
    exact this.congr_deriv (by simp; ring)
  have hpoly : HasDerivAt
      (fun x => x ^ 5 / c + 5 * x ^ 4 / c ^ 2 + 20 * x ^ 3 / c ^ 3 +
        60 * x ^ 2 / c ^ 4 + 120 * x / c ^ 5 + 120 / c ^ 6)
      (5 * t ^ 4 / c + 20 * t ^ 3 / c ^ 2 + 60 * t ^ 2 / c ^ 3 +
        120 * t / c ^ 4 + 120 / c ^ 5) t := by
    have d5 := (hasDerivAt_pow 5 t).div_const c
    have d4 := ((hasDerivAt_pow 4 t).const_mul 5).div_const (c ^ 2)
    have d3 := ((hasDerivAt_pow 3 t).const_mul 20).div_const (c ^ 3)
    have d2 := ((hasDerivAt_pow 2 t).const_mul 60).div_const (c ^ 4)
    have d1 := ((hasDerivAt_id t).const_mul 120).div_const (c ^ 5)
    exact (((((d5.add d4).add d3).add d2).add d1).add_const (120 / c ^ 6)).congr_deriv (by ring)
  refine (hexp.mul hpoly).congr_deriv ?_
  field_simp [hc]
  ring

private theorem integral_pow_five_mul_exp_le {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    ∫ t in (0 : ℝ)..a, t ^ 5 * Real.exp (-c * t) ≤ 120 / c ^ 6 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_polyFiveAntideriv hc.ne' t)
    ((by fun_prop : Continuous fun t : ℝ => t ^ 5 * Real.exp (-c * t)).intervalIntegrable _ _)]
  have h0 : polyFiveAntideriv c 0 = -(120 / c ^ 6) := by
    unfold polyFiveAntideriv; simp
  have ha_le : polyFiveAntideriv c a ≤ 0 := by
    unfold polyFiveAntideriv
    have hpos : 0 ≤ a ^ 5 / c + 5 * a ^ 4 / c ^ 2 + 20 * a ^ 3 / c ^ 3 +
        60 * a ^ 2 / c ^ 4 + 120 * a / c ^ 5 + 120 / c ^ 6 := by positivity
    nlinarith [Real.exp_pos (-c * a)]
  rw [h0]
  linarith

/-- **Sharp `L²` norm bound for `sinhTest a δ`:**
`∫ u, sinhTest a δ u ^ 2 ≤ 30 * a ^ 5 * exp(2δa) / δ ^ 6` for `a ≥ 0`, `δ > 0`. -/
theorem integral_sinhTest_sq_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, sinhTest a δ u ^ 2 ≤ 30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 := by
  set g : ℝ → ℝ := fun u => sinhTest a δ u ^ 2
  have hg_cont : Continuous g := (sinhTest_contDiff a δ).continuous.pow 2
  have hg_zero : ∀ u, u ∉ Icc (-a) a → g u = 0 := fun u hu => by
    have habs : a < |u| := by
      by_contra hle; exact hu (abs_le.mp (not_lt.mp hle))
    simp [g, sinhTest_eq_zero ha habs]
  have hrew : ∫ u, g u = ∫ u in (-a)..a, g u := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg_zero,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have heven : ∫ u in (-a)..a, g u = 2 * ∫ u in (0 : ℝ)..a, g u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _)]
    have hneg : ∫ u in (-a)..(0 : ℝ), g u = ∫ u in (0 : ℝ)..a, g u := by
      have := intervalIntegral.integral_comp_neg g (a := 0) (b := a)
      simp only [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp [g, sinhTest_odd]
    linarith
  have hpt : ∀ u ∈ Icc (0 : ℝ) a, g u ≤
      8 * a ^ 5 * Real.exp (2 * δ * a) * ((a - u) ^ 5 * Real.exp (-(2 * δ) * (a - u))) := by
    intro u ⟨hu0, hua⟩
    have ha2u2 : 0 ≤ a ^ 2 - u ^ 2 := by nlinarith
    have hw_sq : sinhTestWeight a u ^ 2 = (a ^ 2 - u ^ 2) ^ 5 := by
      unfold sinhTestWeight
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ha2u2,
        show (5 / 2 : ℝ) * (2 : ℕ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpoly : (a ^ 2 - u ^ 2) ^ 5 ≤ 32 * a ^ 5 * (a - u) ^ 5 := by
      have hfac : a ^ 2 - u ^ 2 ≤ 2 * a * (a - u) := by nlinarith
      calc (a ^ 2 - u ^ 2) ^ 5 ≤ (2 * a * (a - u)) ^ 5 := pow_le_pow_left₀ ha2u2 hfac 5
        _ = 32 * a ^ 5 * (a - u) ^ 5 := by ring
    have hsh0 : 0 ≤ Real.sinh (δ * u) := Real.sinh_nonneg_iff.mpr (by positivity)
    have hsh : Real.sinh (δ * u) ≤ Real.exp (δ * u) / 2 := by
      rw [Real.sinh_eq]; linarith [Real.exp_pos (-(δ * u))]
    have hsh_sq : Real.sinh (δ * u) ^ 2 ≤
        (1 / 4) * Real.exp (2 * δ * a) * Real.exp (-(2 * δ) * (a - u)) := by
      calc Real.sinh (δ * u) ^ 2 ≤ (Real.exp (δ * u) / 2) ^ 2 := pow_le_pow_left₀ hsh0 hsh 2
        _ = (1 / 4) * (Real.exp (δ * u) * Real.exp (δ * u)) := by ring
        _ = (1 / 4) * Real.exp (2 * δ * u) := by
            rw [← Real.exp_add, show δ * u + δ * u = 2 * δ * u by ring]
        _ = (1 / 4) * (Real.exp (2 * δ * a) * Real.exp (-(2 * δ) * (a - u))) := by
            rw [← Real.exp_add]
            congr 2; ring
        _ = (1 / 4) * Real.exp (2 * δ * a) * Real.exp (-(2 * δ) * (a - u)) := by ring
    calc g u = Real.sinh (δ * u) ^ 2 * sinhTestWeight a u ^ 2 := by
          dsimp [g, sinhTest]; ring
      _ = Real.sinh (δ * u) ^ 2 * (a ^ 2 - u ^ 2) ^ 5 := by rw [hw_sq]
      _ ≤ ((1 / 4) * Real.exp (2 * δ * a) * Real.exp (-(2 * δ) * (a - u))) *
            (32 * a ^ 5 * (a - u) ^ 5) :=
          mul_le_mul hsh_sq hpoly (pow_nonneg ha2u2 5) (by positivity)
      _ = 8 * a ^ 5 * Real.exp (2 * δ * a) * ((a - u) ^ 5 * Real.exp (-(2 * δ) * (a - u))) := by
          ring
  have hint_le : ∫ u in (0 : ℝ)..a, g u ≤
      8 * a ^ 5 * Real.exp (2 * δ * a) *
        ∫ u in (0 : ℝ)..a, (a - u) ^ 5 * Real.exp (-(2 * δ) * (a - u)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha (hg_cont.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun u =>
        8 * a ^ 5 * Real.exp (2 * δ * a) *
          ((a - u) ^ 5 * Real.exp (-(2 * δ) * (a - u)))).intervalIntegrable _ _) hpt
  have hsub_int : (∫ u in (0 : ℝ)..a, (a - u) ^ 5 * Real.exp (-(2 * δ) * (a - u))) =
      ∫ t in (0 : ℝ)..a, t ^ 5 * Real.exp (-(2 * δ) * t) := by
    simpa [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left (a := 0) (b := a)
        (fun t => t ^ 5 * Real.exp (-(2 * δ) * t)) a
  have hexp_int := integral_pow_five_mul_exp_le (show 0 < 2 * δ by positivity) ha
  rw [hrew, heven]
  calc 2 * ∫ u in (0 : ℝ)..a, g u
      ≤ 2 * (8 * a ^ 5 * Real.exp (2 * δ * a) *
          ∫ t in (0 : ℝ)..a, t ^ 5 * Real.exp (-(2 * δ) * t)) := by
        rw [← hsub_int]; linarith
    _ ≤ 2 * (8 * a ^ 5 * Real.exp (2 * δ * a) * (120 / (2 * δ) ^ 6)) := by
        gcongr
    _ = 30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 := by field_simp [hδ.ne']; ring

/-- `L²` norm bound for the modulated `sinhTest`. -/
theorem integral_norm_sq_modulatedTest_sinhTest_le (γ₀ : ℝ) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, ‖modulatedTest γ₀ (sinhTest a δ) u‖ ^ 2 ≤
      30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 := by
  have hpt : (fun u => ‖modulatedTest γ₀ (sinhTest a δ) u‖ ^ 2) = fun u => sinhTest a δ u ^ 2 := by
    funext u
    simp only [modulatedTest, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, one_mul, sq_abs]
  rw [hpt]
  exact integral_sinhTest_sq_le ha hδ

/-- **Optimal tilted signal lower bound (`w = 1/(4δ)`):** for `0 < δ` and `2 ≤ δa`,
`a⁵ e^{4δa} / (2^{26} δ⁷) ≤ (∫ sinhTest a δ u · sinh(δu))²`. -/
theorem sinhTest_energy_sq_ge {a δ : ℝ} (hδ : 0 < δ) (hδa : 2 ≤ δ * a) :
    a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7) ≤
      (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 := by
  have ha : 0 < a := by
    by_contra hle; push Not at hle; nlinarith
  set w := 1 / (4 * δ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hwa : w ≤ a / 4 := by
    dsimp [w]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hP := sinhTest_energy_ge hδ hw hwa
  set x := δ * (a - 2 * w)
  have hx_eq : x = δ * a - 1 / 2 := by
    dsimp [x, w]; field_simp [hδ.ne']; ring
  have hx_ge : 3 / 2 ≤ x := by linarith
  have hexp_2x : 2 ≤ Real.exp (2 * x) := by
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 1 ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hexp_neg_x : Real.exp (-x) ≤ Real.exp x / 2 := by
    have hprod : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_right hexp_2x (Real.exp_pos (-x)).le
    rw [hprod] at this
    linarith
  have hsinh_x : Real.exp x / 4 ≤ Real.sinh x := by
    rw [Real.sinh_eq]; linarith
  have hexp_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by
      rw [sq, ← Real.exp_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      linarith [Real.exp_one_lt_d9]
    have hlt2 : Real.exp (1 / 2 : ℝ) < 2 := by
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith [hlt2]
  have hexp_x : Real.exp (δ * a) / 2 ≤ Real.exp x := by
    rw [hx_eq, show δ * a - (1 / 2 : ℝ) = δ * a + -(1 / 2 : ℝ) by ring, Real.exp_add]
    have := mul_le_mul_of_nonneg_left hexp_half (Real.exp_pos (δ * a)).le
    linarith
  have hsinh_lb : Real.exp (δ * a) / 8 ≤ Real.sinh x := by linarith
  have hsh_sq : (Real.exp (δ * a) / 8) ^ 2 ≤ Real.sinh x ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsinh_lb 2
  have hwa_sq : ((w * a) ^ (5 / 2 : ℝ)) ^ 2 = (w * a) ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
      show (5 / 2 : ℝ) * (2 : ℕ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP2 := pow_le_pow_left₀ (by positivity) hP 2
  refine le_trans ?_ hP2
  calc a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)
      = w ^ 2 * (w * a) ^ 5 * ((Real.exp (δ * a) / 8) ^ 2) ^ 2 := by
        dsimp [w]
        have he4 : Real.exp (4 * δ * a) = Real.exp (δ * a) ^ 4 := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [he4]
        field_simp [hδ.ne']
        ring
    _ = (w * (w * a) ^ (5 / 2 : ℝ) * (Real.exp (δ * a) / 8) ^ 2) ^ 2 := by
        rw [mul_pow, mul_pow, hwa_sq]; ring
    _ ≤ (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh x ^ 2) ^ 2 := by
        gcongr

/-! ### 3. Coherent off-line cone formula and general RvM cluster exclusion -/

/-- For an odd real test `s` supported in `[−a, a]`, the transform at `Δ + iy` splits into its
`sinh · cos` real part and `cosh · sin` imaginary part. -/
theorem paperFT_odd_add_I_mul {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) (Δ y : ℝ) :
    paperFT (fun u => (s u : ℂ)) ((Δ : ℂ) + I * y) =
      -((∫ u, s u * Real.sinh (y * u) * Real.cos (Δ * u) : ℝ) : ℂ) +
        I * ((∫ u, s u * Real.cosh (y * u) * Real.sin (Δ * u) : ℝ) : ℂ) := by
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hint_cc : Integrable (fun u => s u * Real.cosh (y * u) * Real.cos (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  have hint_sc : Integrable (fun u => s u * Real.sinh (y * u) * Real.cos (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  have hint_cs : Integrable (fun u => s u * Real.cosh (y * u) * Real.sin (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  have hint_ss : Integrable (fun u => s u * Real.sinh (y * u) * Real.sin (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  have hodd_cc : ∫ u, s u * Real.cosh (y * u) * Real.cos (Δ * u) = 0 := by
    have h := integral_neg_eq_self (fun u => s u * Real.cosh (y * u) * Real.cos (Δ * u)) volume
    simp only [hodd, mul_neg, Real.cosh_neg, Real.cos_neg, neg_mul] at h
    rw [integral_neg] at h
    linarith
  have hodd_ss : ∫ u, s u * Real.sinh (y * u) * Real.sin (Δ * u) = 0 := by
    have h := integral_neg_eq_self (fun u => s u * Real.sinh (y * u) * Real.sin (Δ * u)) volume
    simp only [hodd, mul_neg, Real.sinh_neg, Real.sin_neg, neg_mul, neg_neg] at h
    rw [integral_neg] at h
    linarith
  have hexp : ∀ u : ℝ, (s u : ℂ) * cexp (I * ((Δ : ℂ) + I * y) * u) =
      (((s u * Real.cosh (y * u) * Real.cos (Δ * u) -
          s u * Real.sinh (y * u) * Real.cos (Δ * u)) : ℝ) : ℂ) +
      I * (((s u * Real.cosh (y * u) * Real.sin (Δ * u) -
          s u * Real.sinh (y * u) * Real.sin (Δ * u)) : ℝ) : ℂ) := fun u => by
    have hI : I * I = -1 := Complex.I_mul_I
    have he1 : I * ((Δ : ℂ) + I * y) * u = (-(y * u) : ℝ) + ((Δ * u : ℝ) : ℂ) * I := by
      push_cast; linear_combination ((y : ℂ) * u) * hI
    rw [he1, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Real.cosh_sub_sinh]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    push_cast
    ring
  rw [paperFT_def]
  simp_rw [hexp]
  have hre_int : Integrable (fun u => (((s u * Real.cosh (y * u) * Real.cos (Δ * u) -
      s u * Real.sinh (y * u) * Real.cos (Δ * u)) : ℝ) : ℂ)) :=
    (hint_cc.sub hint_sc).ofReal
  have him_int : Integrable (fun u => I * (((s u * Real.cosh (y * u) * Real.sin (Δ * u) -
      s u * Real.sinh (y * u) * Real.sin (Δ * u)) : ℝ) : ℂ)) :=
    ((hint_cs.sub hint_ss).ofReal).const_mul I
  rw [integral_add hre_int him_int, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_sub hint_cc hint_sc, integral_sub hint_cs hint_ss,
    hodd_cc, hodd_ss, zero_sub, sub_zero, Complex.ofReal_neg]

/-- Exact real part of the `Wsummand` of `ρ` and `reflect ρ` for any odd real test `s`. -/
theorem re_Wsummand_modulatedTest_odd (Z : ZeroConfig) (γ₀ : ℝ) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    {ε : ℝ} (hre : ρ.re = 1 / 2 + ε) {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) :
    (Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ).re =
        (Z.mult ρ : ℝ) * ((∫ u, s u * Real.cosh (ε * u) * Real.sin ((ρ.im - γ₀) * u)) ^ 2 -
          (∫ u, s u * Real.sinh (ε * u) * Real.cos ((ρ.im - γ₀) * u)) ^ 2) ∧
      (Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) (reflect ρ)).re =
        (Z.mult ρ : ℝ) * ((∫ u, s u * Real.cosh (ε * u) * Real.sin ((ρ.im - γ₀) * u)) ^ 2 -
          (∫ u, s u * Real.sinh (ε * u) * Real.cos ((ρ.im - γ₀) * u)) ^ 2) := by
  set Δ := ρ.im - γ₀
  have hg1 : gammaOf ρ - γ₀ = (Δ : ℂ) + I * (-ε) := by
    apply Complex.ext
    · simp [WeilEF.gammaOf_re, Δ]
    · simp [WeilEF.gammaOf_im, hre]
  have hg2 : conj (gammaOf ρ) - γ₀ = (Δ : ℂ) + I * ε := by
    apply Complex.ext
    · simp [WeilEF.gammaOf_re, Δ]
    · simp [WeilEF.gammaOf_im, hre]
  have hr1 : gammaOf (reflect ρ) - γ₀ = (Δ : ℂ) + I * ε := by
    rw [gammaOf_reflect_eq_conj, hg2]
  have hr2 : conj (gammaOf (reflect ρ)) - γ₀ = (Δ : ℂ) + I * (-ε) := by
    rw [gammaOf_reflect_eq_conj, Complex.conj_conj, hg1]
  have hft_pos := paperFT_odd_add_I_mul hs hsupp hodd Δ ε
  have hft_neg := paperFT_odd_add_I_mul hs hsupp hodd Δ (-ε)
  have hsh_neg : (∫ u, s u * Real.sinh (-ε * u) * Real.cos (Δ * u)) =
      -(∫ u, s u * Real.sinh (ε * u) * Real.cos (Δ * u)) := by
    rw [← integral_neg]
    congr 1 with u
    rw [neg_mul, Real.sinh_neg]
    ring
  have hch_neg : (∫ u, s u * Real.cosh (-ε * u) * Real.sin (Δ * u)) =
      ∫ u, s u * Real.cosh (ε * u) * Real.sin (Δ * u) := by
    congr 1 with u
    rw [neg_mul, Real.cosh_neg]
  simp only [hsh_neg, hch_neg, Complex.ofReal_neg, neg_neg] at hft_neg
  set A := ∫ u, s u * Real.sinh (ε * u) * Real.cos (Δ * u)
  set B := ∫ u, s u * Real.cosh (ε * u) * Real.sin (Δ * u)
  constructor
  · rw [Wsummand_modulatedTest, hg1, hg2, hft_neg, hft_pos, ← Complex.ofReal_natCast]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im, Complex.neg_im]
    ring
  · rw [Wsummand_modulatedTest, hr1, hr2, hft_pos, hft_neg, Z.mult_reflect ρ hρ,
      ← Complex.ofReal_natCast]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im, Complex.neg_im]
    ring

/-- Unified pointwise cone inequality covering both deep coherent cones (`2 ≤ εa`, `|Δ| ≤ 1/(4a)`)
and shallow sub-depth cones (`εa ≤ 1`, `|Δ| ≤ ε/4`). -/
theorem abs_sin_mul_cosh_le_half_sinh {a u ε Δ : ℝ} (hu : |u| ≤ a) (hε : 0 < ε)
    (hcone : (2 ≤ ε * a ∧ |Δ| ≤ 1 / (4 * a)) ∨ (ε * a ≤ 1 ∧ |Δ| ≤ ε / 4)) :
    |Real.sin (Δ * u)| * Real.cosh (ε * |u|) ≤ (1 / 2) * Real.sinh (ε * |u|) ∧
      3 / 4 ≤ Real.cos (Δ * u) := by
  have ha : 0 ≤ a := (abs_nonneg u).trans hu
  have hΔu : |Δ * u| ≤ 1 / 4 := by
    rw [abs_mul]
    rcases hcone with ⟨hεa, hΔ⟩ | ⟨hεa, hΔ⟩
    · have hapos : 0 < a := by
        by_contra hle; push Not at hle; nlinarith
      calc |Δ| * |u| ≤ (1 / (4 * a)) * a := mul_le_mul hΔ hu (abs_nonneg _) (by positivity)
        _ = 1 / 4 := by field_simp [hapos.ne']
    · calc |Δ| * |u| ≤ (ε / 4) * a := mul_le_mul hΔ hu (abs_nonneg _) (by positivity)
        _ ≤ 1 / 4 := by linarith
  have hcos : 3 / 4 ≤ Real.cos (Δ * u) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := Δ * u)
    have h2 : (Δ * u) ^ 2 ≤ (1 / 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hΔu 2
    linarith
  refine ⟨?_, hcos⟩
  have hsin : |Real.sin (Δ * u)| ≤ |Δ| * |u| := by
    rw [← abs_mul]; exact Real.abs_sin_le_abs
  have hsinh_ge : ∀ t : ℝ, 0 ≤ t → t ≤ Real.sinh t := fun t ht => by
    have h := cube_div_six_le_sinh_sub ht
    have : 0 ≤ t ^ 3 / 6 := by positivity
    linarith
  rcases le_or_gt (ε * |u|) 1 with hsmall | hlarge
  · have hcosh1 : Real.cosh (ε * |u|) ≤ 2 := by
      have hc1 : Real.cosh (ε * |u|) ≤ Real.cosh 1 := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_one]
        exact hsmall
      have hc2 : Real.cosh 1 ≤ 2 := by
        rw [Real.cosh_eq]
        have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have he2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        linarith
      exact hc1.trans hc2
    have hΔ_le : |Δ| ≤ ε / 4 := by
      rcases hcone with ⟨hεa, hΔ⟩ | ⟨_, hΔ⟩
      · have hapos : 0 < a := by
          by_contra hle; push Not at hle; nlinarith
        have : 1 / (4 * a) ≤ ε / 8 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
      · exact hΔ
    calc |Real.sin (Δ * u)| * Real.cosh (ε * |u|)
        ≤ (|Δ| * |u|) * 2 := mul_le_mul hsin hcosh1 (Real.cosh_pos _).le (by positivity)
      _ ≤ (ε / 4 * |u|) * 2 := by gcongr
      _ = (1 / 2) * (ε * |u|) := by ring
      _ ≤ (1 / 2) * Real.sinh (ε * |u|) :=
          mul_le_mul_of_nonneg_left (hsinh_ge _ (by positivity)) (by norm_num)
  · rcases hcone with ⟨_, _⟩ | ⟨hεa, _⟩
    · have hexp2 : 3 ≤ Real.exp (2 * (ε * |u|)) := by
        have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have h2 : Real.exp 2 ≤ Real.exp (2 * (ε * |u|)) := Real.exp_le_exp.mpr (by linarith)
        have h4 : (4 : ℝ) < Real.exp 2 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith [Real.exp_pos 1]
        linarith
      have hcosh_le : Real.cosh (ε * |u|) ≤ 2 * Real.sinh (ε * |u|) := by
        rw [Real.cosh_eq, Real.sinh_eq]
        have hprod : Real.exp (2 * (ε * |u|)) * Real.exp (-(ε * |u|)) = Real.exp (ε * |u|) := by
          rw [← Real.exp_add]; congr 1; ring
        have := mul_le_mul_of_nonneg_right hexp2 (Real.exp_pos (-(ε * |u|))).le
        rw [hprod] at this
        linarith
      have hΔu' : |Δ| * |u| ≤ 1 / 4 := by rwa [abs_mul] at hΔu
      have hsh0 : 0 ≤ Real.sinh (ε * |u|) := Real.sinh_nonneg_iff.mpr (by positivity)
      calc |Real.sin (Δ * u)| * Real.cosh (ε * |u|)
          ≤ (|Δ| * |u|) * (2 * Real.sinh (ε * |u|)) :=
            mul_le_mul hsin hcosh_le (Real.cosh_pos _).le (by positivity)
        _ ≤ (1 / 4) * (2 * Real.sinh (ε * |u|)) :=
            mul_le_mul_of_nonneg_right hΔu' (by positivity)
        _ = (1 / 2) * Real.sinh (ε * |u|) := by ring
    · exfalso
      have : ε * |u| ≤ ε * a := mul_le_mul_of_nonneg_left hu hε.le
      linarith

/-- **Coherent pair negativity inequality.** For an odd real continuous `s` supported in `[−a, a]`
with `0 ≤ s u` for `u ≥ 0`, every off-line zero `ρ = ½ + ε + iγ` (`ε > 0`) in the cone of
`abs_sin_mul_cosh_le_half_sinh` satisfies
`Re(Wsummand ρ + Wsummand (reflect ρ)) ≤ −(5/8) m_ρ (∫ s(u) sinh(εu))²`. -/
theorem re_Wsummand_pair_modulatedTest_le (Z : ZeroConfig) (γ₀ : ℝ) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    {ε : ℝ} (hε : 0 < ε) (hre : ρ.re = 1 / 2 + ε) {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u)
    (hnonneg : ∀ u, 0 ≤ u → 0 ≤ s u)
    (hcone : (2 ≤ ε * a ∧ |ρ.im - γ₀| ≤ 1 / (4 * a)) ∨ (ε * a ≤ 1 ∧ |ρ.im - γ₀| ≤ ε / 4)) :
    (Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ).re +
        (Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) (reflect ρ)).re ≤
      -(5 / 8) * (Z.mult ρ : ℝ) * (∫ u, s u * Real.sinh (ε * u)) ^ 2 := by
  obtain ⟨hr1, hr2⟩ := re_Wsummand_modulatedTest_odd Z γ₀ hρ hre hs hsupp hodd
  set Δ := ρ.im - γ₀
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hprod_nonneg : ∀ u, 0 ≤ s u * Real.sinh (ε * u) := fun u => by
    rcases le_or_gt 0 u with hu | hu
    · exact mul_nonneg (hnonneg u hu) (Real.sinh_nonneg_iff.mpr (by positivity))
    · have hsu : s u = -s (-u) := by linarith [hodd u]
      have hsh : Real.sinh (ε * u) = -Real.sinh (ε * (-u)) := by
        rw [mul_neg, Real.sinh_neg, neg_neg]
      rw [hsu, hsh, neg_mul_neg]
      exact mul_nonneg (hnonneg (-u) (by linarith))
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hε.le (by linarith)))
  have hs_abs : ∀ u, |s u| * Real.sinh (ε * |u|) = s u * Real.sinh (ε * u) := fun u => by
    rcases le_or_gt 0 u with hu | hu
    · rw [abs_of_nonneg hu, abs_of_nonneg (hnonneg u hu)]
    · have hsu : s u = -s (-u) := by linarith [hodd u]
      rw [abs_of_neg hu, hsu, abs_neg, abs_of_nonneg (hnonneg (-u) (by linarith)),
        show ε * u = -(ε * -u) by ring, Real.sinh_neg, neg_mul_neg]
  have hint_sh : Integrable (fun u => s u * Real.sinh (ε * u)) :=
    (hs.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hint_A : Integrable (fun u => s u * Real.sinh (ε * u) * Real.cos (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  have hint_B : Integrable (fun u => s u * Real.cosh (ε * u) * Real.sin (Δ * u)) :=
    ((hs.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
      hcs.mul_right.mul_right
  set P := ∫ u, s u * Real.sinh (ε * u)
  have hP0 : 0 ≤ P := integral_nonneg hprod_nonneg
  have hA_ge : (3 / 4) * P ≤ ∫ u, s u * Real.sinh (ε * u) * Real.cos (Δ * u) := by
    dsimp only [P]
    rw [← integral_const_mul]
    refine integral_mono (hint_sh.const_mul (3 / 4)) hint_A fun u => ?_
    by_cases h0 : s u = 0
    · simp [h0]
    · obtain ⟨_, hcos⟩ := abs_sin_mul_cosh_le_half_sinh (hsupp u h0) hε hcone
      exact (mul_le_mul_of_nonneg_left hcos (hprod_nonneg u)).trans_eq (by ring)
  have hB_le : |∫ u, s u * Real.cosh (ε * u) * Real.sin (Δ * u)| ≤ (1 / 2) * P := by
    refine (abs_integral_le_integral_abs).trans ?_
    dsimp only [P]
    rw [← integral_const_mul]
    refine integral_mono hint_B.abs (hint_sh.const_mul _) fun u => ?_
    by_cases h0 : s u = 0
    · simp [h0]
    · obtain ⟨hsin, _⟩ := abs_sin_mul_cosh_le_half_sinh (hsupp u h0) hε hcone
      rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _), ← Real.cosh_abs, abs_mul,
        abs_of_pos hε]
      calc |s u| * Real.cosh (ε * |u|) * |Real.sin (Δ * u)|
          = |s u| * (|Real.sin (Δ * u)| * Real.cosh (ε * |u|)) := by ring
        _ ≤ |s u| * ((1 / 2) * Real.sinh (ε * |u|)) :=
            mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
        _ = (1 / 2) * (|s u| * Real.sinh (ε * |u|)) := by ring
        _ = (1 / 2) * (s u * Real.sinh (ε * u)) := by rw [hs_abs]
  have hB_sq : (∫ u, s u * Real.cosh (ε * u) * Real.sin (Δ * u)) ^ 2 ≤ ((1 / 2) * P) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hB_le 2
  have hA_sq : ((3 / 4) * P) ^ 2 ≤ (∫ u, s u * Real.sinh (ε * u) * Real.cos (Δ * u)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA_ge 2
  have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  rw [hr1, hr2]
  nlinarith

/-! ### 4. Near-background `L²` sampling and general RvM cluster exclusion -/

/-- Unit-window multiplicity bound on a finite set of zeros in `[γ₀ − R, γ₀ + R]`. -/
theorem sum_mult_unit_ball_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ R : ℝ} (hR : 0 ≤ R) (F : Finset ℂ) (hFc : ∀ ρ ∈ F, ρ ∈ Z.carrier)
    (hFr : ∀ ρ ∈ F, |ρ.im - γ₀| ≤ R) (T : ℝ) :
    (∑ ρ ∈ F with |ρ.im - T| ≤ 1, Z.mult ρ) ≤
      ⌈3 * A₀ * Real.log (|γ₀| + R + 6)⌉₊ := by
  classical
  set P := F.filter (fun ρ => |ρ.im - T| ≤ 1)
  by_cases hne : P.Nonempty
  · obtain ⟨ρ₁, hρ₁⟩ := hne
    have hρ₁F : ρ₁ ∈ F := (Finset.mem_filter.mp hρ₁).1
    have hρ₁T : |ρ₁.im - T| ≤ 1 := (Finset.mem_filter.mp hρ₁).2
    have hρ₁R : |ρ₁.im - γ₀| ≤ R := hFr ρ₁ hρ₁F
    have hTabs : |T| ≤ |γ₀| + R + 1 := by
      have h1 := abs_sub_le T ρ₁.im 0
      have h2 := abs_sub_le ρ₁.im γ₀ 0
      simp only [sub_zero] at h1 h2
      rw [abs_sub_comm] at h1
      linarith
    have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc
    have hpiece : ∀ t₀ : ℝ, |t₀ - T| ≤ 3 / 2 →
        ∀ Q : Finset ℂ, Q ⊆ P → (∀ ρ ∈ Q, t₀ < ρ.im ∧ ρ.im ≤ t₀ + 1) →
          (∑ ρ ∈ Q, (Z.mult ρ : ℝ)) ≤ A₀ * Real.log (|γ₀| + R + 6) := by
      intro t₀ ht₀ Q hQP hQint
      have hQsub : ∀ ρ ∈ Q, ρ ∈ Z.carrier := fun ρ hρ =>
        hFc ρ (Finset.mem_filter.mp (hQP hρ)).1
      set Q' : Finset Z.carrier := Q.subtype (· ∈ Z.carrier)
      have hsum_eq : (∑ ρ ∈ Q, (Z.mult ρ : ℝ)) = ∑ ρ ∈ Q', (Z.mult ρ : ℝ) := by
        dsimp only [Q']
        exact (Finset.sum_subtype_of_mem _ hQsub).symm
      rw [hsum_eq]
      refine (hLC.window t₀ Q' fun ρ hρ => hQint ρ (Finset.mem_subtype.mp hρ)).trans ?_
      have ht₀_abs : |t₀| + 3 ≤ |γ₀| + R + 6 := by
        have := abs_sub_le t₀ T 0
        simp only [sub_zero] at this
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) ht₀_abs) (by linarith)
    set Q₁ := P.filter (fun ρ => ρ.im ≤ T - 1 / 2)
    set Q₂ := P.filter (fun ρ => T - 1 / 2 < ρ.im ∧ ρ.im ≤ T + 1 / 2)
    set Q₃ := P.filter (fun ρ => T + 1 / 2 < ρ.im)
    have h1 := hpiece (T - 3 / 2) (by norm_num) Q₁ (Finset.filter_subset _ _) fun ρ hρ => by
      obtain ⟨hP, hle⟩ := Finset.mem_filter.mp hρ
      have := abs_le.mp (Finset.mem_filter.mp hP).2
      exact ⟨by linarith, by linarith⟩
    have h2 := hpiece (T - 1 / 2) (by norm_num) Q₂ (Finset.filter_subset _ _) fun ρ hρ => by
      obtain ⟨_, hgt, hle⟩ := Finset.mem_filter.mp hρ
      exact ⟨hgt, by linarith⟩
    have h3 := hpiece (T + 1 / 2) (by norm_num) Q₃ (Finset.filter_subset _ _) fun ρ hρ => by
      obtain ⟨hP, hgt⟩ := Finset.mem_filter.mp hρ
      have := abs_le.mp (Finset.mem_filter.mp hP).2
      exact ⟨hgt, by linarith⟩
    have hcover : (∑ ρ ∈ P, (Z.mult ρ : ℝ)) ≤
        (∑ ρ ∈ Q₁, (Z.mult ρ : ℝ)) + (∑ ρ ∈ Q₂, (Z.mult ρ : ℝ)) +
          (∑ ρ ∈ Q₃, (Z.mult ρ : ℝ)) := by
      simp only [Q₁, Q₂, Q₃, Finset.sum_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ρ _ => ?_
      have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
      by_cases ha1 : ρ.im ≤ T - 1 / 2
      · rw [if_pos ha1]; split_ifs <;> linarith
      · by_cases ha2 : ρ.im ≤ T + 1 / 2
        · rw [if_neg ha1, if_pos ⟨lt_of_not_ge ha1, ha2⟩]; split_ifs <;> linarith
        · rw [if_neg ha1, if_neg (fun h => ha2 h.2), if_pos (lt_of_not_ge ha2)]; split_ifs <;> linarith
    have hreal : ((∑ ρ ∈ P, Z.mult ρ : ℕ) : ℝ) ≤ 3 * A₀ * Real.log (|γ₀| + R + 6) := by
      rw [Nat.cast_sum]
      linarith
    exact Nat.le_ceil _ |>.trans' (by exact_mod_cast le_rfl) |>.trans' (by
      exact Nat.cast_le.mp (hreal.trans (Nat.le_ceil _)))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    change ∑ ρ ∈ P, Z.mult ρ ≤ _
    rw [hne, Finset.sum_empty]
    exact Nat.zero_le _

/-- **`L²` sampling bound on near background zeros.** For any `C²` (or continuous) test `f`
supported in `[−a, a]` (`a > 0`) and any finite subset `F ⊆ Z.carrier` in `[γ₀ − R, γ₀ + R]` whose
zeros satisfy `|ρ.re − ½| ≤ σ`,
`∑_{ρ ∈ F} ‖Z.Wsummand f f ρ‖ ≤ 4 A₀ log(|γ₀| + R + 6) (2a + 2π) e^{2π} e^{2σa} ∫ ‖f‖²`. -/
theorem sum_norm_Wsummand_near_le_of_depth_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {a γ₀ R σ : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hσ : 0 ≤ σ) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) (F : Finset ℂ) (hFc : ∀ ρ ∈ F, ρ ∈ Z.carrier)
    (hFr : ∀ ρ ∈ F, |ρ.im - γ₀| ≤ R) (hFσ : ∀ ρ ∈ F, |ρ.re - 1 / 2| ≤ σ) :
    ∑ ρ ∈ F, ‖Z.Wsummand f f ρ‖ ≤
      4 * A₀ * Real.log (|γ₀| + R + 6) *
        ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 := by
  classical
  have hf_src : IntervalSource a f :=
    { continuous := hf
      hasCompactSupport := hasCompactSupport_of_tsupport_subset_Icc hfs
      vanish := fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (hfs hm) }
  let ι := Σ ρ : F, Fin (Z.mult ρ)
  set M := ⌈3 * A₀ * Real.log (|γ₀| + R + 6)⌉₊
  let x : ι → ℝ := fun q => (q.1 : ℂ).im
  have hcard : ∀ T : ℝ, (((Finset.univ : Finset ι) : Set ι) ∩ {q | |x q - T| ≤ 1}).encard ≤ M := by
    intro T
    set sT : Finset ι := Finset.univ.filter (fun q => |x q - T| ≤ 1)
    have hset : (((Finset.univ : Finset ι) : Set ι) ∩ {q | |x q - T| ≤ 1}) = (sT : Set ι) := by
      ext q; simp [sT]
    rw [hset, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (by
      have hcard_eq : sT.card = ∑ ρ ∈ F with |ρ.im - T| ≤ 1, Z.mult ρ := by
        rw [Finset.card_eq_sum_ones, show sT = Finset.univ.filter (fun q : ι => |x q - T| ≤ 1) from rfl,
          Finset.sum_filter, Fintype.sum_sigma]
        simp only [x, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        rw [Finset.sum_filter, ← Finset.univ_eq_attach]
        exact (Finset.sum_attach F fun ρ => if |ρ.im - T| ≤ 1 then Z.mult ρ else 0).trans rfl
      rw [hcard_eq]
      exact sum_mult_unit_ball_le Z hA₀ hloc hR F hFc hFr T)
  let y₁ : ι → ℝ := fun q => 1 / 2 - (q.1 : ℂ).re
  let y₂ : ι → ℝ := fun q => (q.1 : ℂ).re - 1 / 2
  have hy₁ : ∀ q, |y₁ q| ≤ σ := fun q => by
    dsimp [y₁]; rw [abs_sub_comm]; exact hFσ q.1 q.1.2
  have hy₂ : ∀ q, |y₂ q| ≤ σ := fun q => hFσ q.1 q.1.2
  have hs₁ := sum_norm_sq_testTransform_le_of_locallyBounded' ha hf_src x y₁ hσ hy₁ Finset.univ hcard
  have hs₂ := sum_norm_sq_testTransform_le_of_locallyBounded' ha hf_src x y₂ hσ hy₂ Finset.univ hcard
  have hft_eq : ∀ z, paperFT f z = testTransform f z := fun _ => rfl
  have hsum₁ : (∑ q : ι, ‖testTransform f ((x q : ℂ) + (y₁ q : ℂ) * I)‖ ^ 2) =
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 := by
    rw [Finset.sum_sigma']
    simp only [Finset.univ_eq_attach, x, y₁, hft_eq]
    refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
      (Finset.sum_attach F fun ρ => (Z.mult ρ : ℝ) * ‖testTransform f (gammaOf ρ)‖ ^ 2)
    have hg : ((ρ : ℂ).im : ℂ) + ((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) * I = gammaOf ρ := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    simp [hg, Finset.sum_const, nsmul_eq_mul]
  have hsum₂ : (∑ q : ι, ‖testTransform f ((x q : ℂ) + (y₂ q : ℂ) * I)‖ ^ 2) =
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2 := by
    rw [Finset.sum_sigma']
    simp only [Finset.univ_eq_attach, x, y₂, hft_eq]
    refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
      (Finset.sum_attach F fun ρ => (Z.mult ρ : ℝ) * ‖testTransform f (conj (gammaOf ρ))‖ ^ 2)
    have hg : ((ρ : ℂ).im : ℂ) + (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) * I = conj (gammaOf ρ) := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    simp [hg, Finset.sum_const, nsmul_eq_mul]
  rw [hsum₁] at hs₁
  rw [hsum₂] at hs₂
  have hpt : ∀ ρ ∈ F, ‖Z.Wsummand f f ρ‖ ≤
      (1 / 2) * ((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
        (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := fun ρ _ => by
    rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    nlinarith [sq_nonneg (‖paperFT f (gammaOf ρ)‖ - ‖paperFT f (conj (gammaOf ρ))‖)]
  have hM_le : (M : ℝ) ≤ 4 * A₀ * Real.log (|γ₀| + R + 6) := by
    have hlog1 : 1 ≤ Real.log (|γ₀| + R + 6) := by
      have := one_le_log_abs_add_three γ₀
      exact this.trans (Real.log_le_log (by positivity) (by linarith))
    have hlt := (Nat.ceil_lt_add_one (show 0 ≤ 3 * A₀ * Real.log (|γ₀| + R + 6) by positivity)).le
    dsimp [M]
    nlinarith
  have hcoeff0 : 0 ≤ ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
      ∫ u, ‖f u‖ ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  calc ∑ ρ ∈ F, ‖Z.Wsummand f f ρ‖
      ≤ ∑ ρ ∈ F, (1 / 2) * ((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
          (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := Finset.sum_le_sum hpt
    _ = (1 / 2) * ((∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2) +
          (∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (M : ℝ) * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 := by
        linarith
    _ ≤ 4 * A₀ * Real.log (|γ₀| + R + 6) *
          ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * ∫ u, ‖f u‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hM_le hcoeff0
        linarith

/-- Far-tail pointwise bound: for `R < |ρ.im − γ₀|`, one power of `1 + |ρ.im − γ₀|` pays `1 + R`. -/
theorem norm_Wsummand_modulatedTest_le_far (Z : ZeroConfig) (γ₀ : ℝ) {s : ℝ → ℝ} {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hfar : R < |ρ.im - γ₀|) :
    ‖Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) *
        ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₀|) ^ 3) := by
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hN := testNorm_nonneg s
  have hE := exp_abs_half_sub_sq_le (Z.strip ρ hρ) ha
  set D := 1 + |ρ.im - γ₀|
  have hDR : 1 + R ≤ D := by dsimp [D]; linarith
  have hR0 : 0 < 1 + R := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  refine (norm_Wsummand_modulatedTest_le Z γ₀ hs hsupp ρ).trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2))
      ≤ (Z.mult ρ : ℝ) * (Real.exp a * (16 * testNorm s ^ 2)) := by gcongr
    _ = 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * ((Z.mult ρ : ℝ) / D ^ 3) *
          ((1 + R) * D ^ 3) := by field_simp
    _ ≤ 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * ((Z.mult ρ : ℝ) / D ^ 3) *
          (D * D ^ 3) := by gcongr
    _ = 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by
        ring

/-- **Master `L²` tilt-amplification inequality for coherent off-line clusters.**
Let `Z` satisfy `N(t, t+1] ≤ A₀ log(|t| + 3)` (`A₀ ≥ 1`), and let `S` be a finite set of off-line
zeros in the coherent cone `ρ.re ≥ ½ + δ`, `|ρ.im − γ₀| ≤ 1/(4a)` (`δ > 0`, `2 ≤ δa`). If every
other zero of `Z` in `[γ₀ − R, γ₀ + R]` (`R ≥ 1/(4a)`) satisfies `|ρ.re − ½| ≤ σ`, then for
`f = modulatedTest γ₀ (sinhTest a δ)` (`P = ∫ sinhTest a δ u · sinh(δu)`):
`Re W_Z(f, f) ≤ −(5/8)(∑_{ρ ∈ S} m_ρ) P² + Near(a, δ, σ, R) + Far(a, δ, R)`. -/
theorem re_W_modulatedTest_coherent_cluster_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a δ R σ : ℝ} (hδ : 0 < δ) (hδa : 2 ≤ δ * a) (hR : 1 / (4 * a) ≤ R) (hσ : 0 ≤ σ)
    (S : Finset ℂ) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hnear : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.im - γ₀| ≤ R →
      |ρ.re - 1 / 2| ≤ σ) :
    (Z.W (modulatedTest γ₀ (sinhTest a δ)) (modulatedTest γ₀ (sinhTest a δ))).re ≤
      -(5 / 8) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) *
          (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 +
        4 * A₀ * Real.log (|γ₀| + R + 6) *
          ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
          (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) +
        384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 *
          (Real.exp a / (1 + R)) := by
  classical
  have ha : 0 < a := by
    by_contra hle; push Not at hle; nlinarith
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  set s := sinhTest a δ
  set f := modulatedTest γ₀ s
  have hs_cd : ContDiff ℝ 2 s := sinhTest_contDiff a δ
  have hs_supp : ∀ u, s u ≠ 0 → |u| ≤ a := sinhTest_supp ha.le
  have hs_odd : ∀ u, s (-u) = -s u := sinhTest_odd a δ
  have hs_nn : ∀ u, 0 ≤ u → 0 ≤ s u := fun u hu =>
    mul_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)) (sinhTestWeight_nonneg a u)
  have hf_cd : ContDiff ℝ 2 f := modulatedTest_contDiff γ₀ hs_cd
  have hf_supp : tsupport f ⊆ Icc (-a) a := tsupport_modulatedTest_subset γ₀ hs_supp
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₀
  have hsumm : Summable (fun τ : Z.carrier => Z.Wsummand f f τ) :=
    Summable.of_norm_bounded (hwsum.mul_left _) fun τ =>
      norm_Wsummand_modulatedTest_le_weight Z γ₀ ha.le hs_cd hs_supp τ.2
  -- Finite window `[γ₀ - R, γ₀ + R]`
  have hfin_set : (Z.carrier ∩ {z : ℂ | γ₀ - R ≤ z.im ∧ z.im ≤ γ₀ + R}).Finite :=
    (Z.finite_window (γ₀ - R - 1) (γ₀ + R)).subset fun z ⟨hz, h1, h2⟩ => ⟨hz, by linarith, h2⟩
  set W_all : Finset ℂ := hfin_set.toFinset
  have hmem_Wall : ∀ z : ℂ, z ∈ W_all ↔ z ∈ Z.carrier ∧ |z.im - γ₀| ≤ R := fun z => by
    rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, abs_le]
    exact ⟨fun ⟨hz, h1, h2⟩ => ⟨hz, by linarith, by linarith⟩,
      fun ⟨hz, h1, h2⟩ => ⟨hz, by linarith, by linarith⟩⟩
  set S' : Finset ℂ := S.image reflect
  have hdisj_SS' : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρ'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hρ'
    have h1 := hSδ _ hρ
    have h2 := hSδ q hq
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at h1
    linarith
  have hrefl_inj : Function.Injective reflect := fun z w h => by
    have h1 : reflect (reflect z) = z := by
      apply Complex.ext <;> simp [reflect]
    have h2 : reflect (reflect w) = w := by
      apply Complex.ext <;> simp [reflect]
    rw [← h1, ← h2, h]
  have hsub_S : S ⊆ W_all := fun ρ hρ =>
    (hmem_Wall ρ).mpr ⟨hSc ρ hρ, (hSγ ρ hρ).trans hR⟩
  have hsub_S' : S' ⊆ W_all := by
    intro ρ hρ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hρ
    refine (hmem_Wall _).mpr ⟨Z.reflect_mem q (hSc q hq), ?_⟩
    have him : (reflect q).im = q.im := by simp [reflect]
    rw [him]
    exact (hSγ q hq).trans hR
  set F_near : Finset ℂ := W_all \ (S ∪ S')
  set P := ∫ u, s u * Real.sinh (δ * u)
  -- Pair bound on each `ρ ∈ S`
  have hpair_le : ∀ ρ ∈ S,
      (Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re ≤
        -(5 / 8) * (Z.mult ρ : ℝ) * P ^ 2 := by
    intro ρ hρ
    set ε := ρ.re - 1 / 2
    have hε_ge : δ ≤ ε := by dsimp [ε]; linarith [hSδ ρ hρ]
    have hε_pos : 0 < ε := hδ.trans_le hε_ge
    have hre : ρ.re = 1 / 2 + ε := by dsimp [ε]; ring
    have hcone : (2 ≤ ε * a ∧ |ρ.im - γ₀| ≤ 1 / (4 * a)) ∨ (ε * a ≤ 1 ∧ |ρ.im - γ₀| ≤ ε / 4) :=
      Or.inl ⟨hδa.trans (mul_le_mul_of_nonneg_right hε_ge ha.le), hSγ ρ hρ⟩
    have h1 := re_Wsummand_pair_modulatedTest_le Z γ₀ (hSc ρ hρ) hε_pos hre
      hs_cd.continuous hs_supp hs_odd hs_nn hcone
    have hP_mono : P ≤ ∫ u, s u * Real.sinh (ε * u) := by
      have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hs_supp
      refine integral_mono
        ((hs_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right)
        ((hs_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right)
        fun u => ?_
      rcases le_or_gt 0 u with hu | hu
      · exact mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hε_ge hu)) (hs_nn u hu)
      · have hsu : s u = -s (-u) := by linarith [hs_odd u]
        rw [hsu, show δ * u = -(δ * -u) by ring, show ε * u = -(ε * -u) by ring,
          Real.sinh_neg, Real.sinh_neg, neg_mul_neg, neg_mul_neg]
        exact mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hε_ge (by linarith)))
          (hs_nn (-u) (by linarith))
    have hP0 : 0 ≤ P := integral_nonneg fun u => by
      rcases le_or_gt 0 u with hu | hu
      · exact mul_nonneg (hs_nn u hu) (Real.sinh_nonneg_iff.mpr (by positivity))
      · have hsu : s u = -s (-u) := by linarith [hs_odd u]
        rw [hsu, show δ * u = -(δ * -u) by ring, Real.sinh_neg, neg_mul_neg]
        exact mul_nonneg (hs_nn (-u) (by linarith)) (Real.sinh_nonneg_iff.mpr (by positivity))
    have hP2 := pow_le_pow_left₀ hP0 hP_mono 2
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    nlinarith
  -- Split `∑' τ : Z.carrier, Re (Wsummand τ)` into `W_all` and its complement
  set Wall_sub : Finset Z.carrier := W_all.subtype (· ∈ Z.carrier)
  have hre_sum : Summable (fun τ : Z.carrier => (Z.Wsummand f f τ).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  have hsplit_tsum : (Z.W f f).re =
      (∑ τ ∈ Wall_sub, (Z.Wsummand f f τ).re) +
        ∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, (Z.Wsummand f f τ).re := by
    rw [ZeroConfig.W, Complex.re_tsum hsumm, ← hre_sum.sum_add_tsum_compl Wall_sub]
    rfl
  have hWall_sum : (∑ τ ∈ Wall_sub, (Z.Wsummand f f τ).re) =
      ∑ ρ ∈ W_all, (Z.Wsummand f f ρ).re := by
    rw [Finset.sum_subtype_of_mem _ fun ρ hρ => ((hmem_Wall ρ).mp hρ).1]
  have hWall_part : W_all = (S ∪ S') ∪ F_near := by
    ext ρ
    simp only [F_near, Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => by tauto, fun h => h.elim (fun h1 => h1.elim (hsub_S ·) (hsub_S' ·)) And.left⟩
  have hdisj_F : Disjoint (S ∪ S') F_near := Finset.disjoint_sdiff
  have hWall_decomp : (∑ ρ ∈ W_all, (Z.Wsummand f f ρ).re) =
      (∑ ρ ∈ S, ((Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re)) +
        ∑ ρ ∈ F_near, (Z.Wsummand f f ρ).re := by
    rw [hWall_part, Finset.sum_union hdisj_F, Finset.sum_union hdisj_SS',
      Finset.sum_image (fun x _ y _ h => hrefl_inj h), ← Finset.sum_add_distrib]
  -- Bound on `S ∪ S'`
  have hS_bound : ∑ ρ ∈ S, ((Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re) ≤
      -(5 / 8) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * P ^ 2 := by
    refine (Finset.sum_le_sum hpair_le).trans_eq ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  -- Bound on `F_near`
  have hF_bound : ∑ ρ ∈ F_near, (Z.Wsummand f f ρ).re ≤
      4 * A₀ * Real.log (|γ₀| + R + 6) *
        ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
        (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) := by
    have h1 : ∑ ρ ∈ F_near, (Z.Wsummand f f ρ).re ≤ ∑ ρ ∈ F_near, ‖Z.Wsummand f f ρ‖ :=
      Finset.sum_le_sum fun ρ _ => Complex.re_le_norm _
    have h2 := sum_norm_Wsummand_near_le_of_depth_le Z hA₀ hloc ha hR0 hσ hf_cd.continuous hf_supp
      F_near (fun ρ hρ => ((hmem_Wall ρ).mp (Finset.sdiff_subset hρ)).1)
      (fun ρ hρ => ((hmem_Wall ρ).mp (Finset.sdiff_subset hρ)).2)
      (fun ρ hρ => by
        obtain ⟨hw, hn⟩ := Finset.mem_sdiff.mp hρ
        rw [Finset.mem_union, not_or] at hn
        obtain ⟨hc, hr⟩ := (hmem_Wall ρ).mp hw
        exact hnear ρ hc hn.1 hn.2 hr)
    have h3 := integral_norm_sq_modulatedTest_sinhTest_le γ₀ ha.le hδ
    refine h1.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- Bound on far tail `τ ∉ Wall_sub`
  have hfar_bound : (∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, (Z.Wsummand f f τ).re) ≤
      384 * A₀ * Real.log (|γ₀| + 3) * testNorm s ^ 2 * (Real.exp a / (1 + R)) := by
    set c_far : Z.carrier → ℝ := fun τ =>
      16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) *
        ((Z.mult τ : ℝ) / (1 + |(τ : ℂ).im - γ₀|) ^ 3)
    have hc_sum : Summable c_far := hwsum.mul_left _
    have hpt_far : ∀ τ : {τ : Z.carrier // τ ∉ Wall_sub},
        (Z.Wsummand f f τ).re ≤ c_far τ.1 := fun τ => by
      have hfar : R < |(τ.1 : ℂ).im - γ₀| := by
        by_contra hle; push Not at hle
        exact τ.2 (Finset.mem_subtype.mpr ((hmem_Wall τ.1).mpr ⟨τ.1.2, hle⟩))
      exact (Complex.re_le_norm _).trans
        (norm_Wsummand_modulatedTest_le_far Z γ₀ ha.le hR0 hs_cd hs_supp τ.1.2 hfar)
    have hle1 : (∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, (Z.Wsummand f f τ).re) ≤
        ∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, c_far τ.1 :=
      Summable.tsum_le_tsum hpt_far (hre_sum.subtype _) (hc_sum.subtype _)
    have hle2 : (∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, c_far τ.1) ≤ ∑' τ : Z.carrier, c_far τ :=
      Summable.tsum_subtype_le hc_sum _ fun τ => by
        dsimp [c_far]; have := testNorm_nonneg s; positivity
    have hle3 : ∑' τ : Z.carrier, c_far τ ≤
        16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * (24 * A₀ * Real.log (|γ₀| + 3)) := by
      dsimp [c_far]
      rw [tsum_mul_left]
      have := testNorm_nonneg s
      exact mul_le_mul_of_nonneg_left hwle (by positivity)
    calc (∑' τ : {τ : Z.carrier // τ ∉ Wall_sub}, (Z.Wsummand f f τ).re)
        ≤ 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * (24 * A₀ * Real.log (|γ₀| + 3)) :=
          hle1.trans (hle2.trans hle3)
      _ = 384 * A₀ * Real.log (|γ₀| + 3) * testNorm s ^ 2 * (Real.exp a / (1 + R)) := by ring
  rw [hsplit_tsum, hWall_sum, hWall_decomp]
  linarith

/-- **Window positivity excludes unshielded coherent clusters (`V1` seeing in general RvM).**
If `WindowPositiveAt Z a` holds on a configuration `Z` with `N(t, t+1] ≤ A₀ log(|t| + 3)`, and `S`
is a coherent cluster (`ρ.re ≥ ½ + δ`, `|ρ.im − γ₀| ≤ 1/(4a)`, `2 ≤ δa`) with near background
depth `≤ σ` on `[γ₀ − R, γ₀ + R]` (`R ≥ 1/(4a)`), then the sharp `L²` tilt inequality cannot be
violated:
`(5/8)(∑_{ρ ∈ S} m_ρ) · a⁵ e^{4δa} / (2^{26} δ⁷) ≤ Near(a, δ, σ, R) + Far(a, δ, R)`. -/
theorem windowPositiveAt_coherent_cluster_bound (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a δ R σ : ℝ} (hδ : 0 < δ) (hδa : 2 ≤ δ * a) (hR : 1 / (4 * a) ≤ R) (hσ : 0 ≤ σ)
    (hpos : WindowPositiveAt Z a)
    (S : Finset ℂ) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hnear : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.im - γ₀| ≤ R →
      |ρ.re - 1 / 2| ≤ σ) :
    (5 / 8) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) ≤
      4 * A₀ * Real.log (|γ₀| + R + 6) *
        ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
        (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) +
      384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (Real.exp a / (1 + R)) := by
  have ha : 0 < a := by
    by_contra hle; push Not at hle; nlinarith
  have h0 : 0 ≤ (Z.W (modulatedTest γ₀ (sinhTest a δ)) (modulatedTest γ₀ (sinhTest a δ))).re :=
    hpos _ (modulatedTest_contDiff γ₀ (sinhTest_contDiff a δ))
      (tsupport_modulatedTest_subset γ₀ (sinhTest_supp ha.le))
  have hW := re_W_modulatedTest_coherent_cluster_le Z hA₀ hloc hδ hδa hR hσ S hSc hSδ hSγ hnear
  have hP2 := sinhTest_energy_sq_ge hδ hδa
  have hmult0 : 0 ≤ ∑ ρ ∈ S, (Z.mult ρ : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hP2 (show 0 ≤ (5 / 8) * ∑ ρ ∈ S, (Z.mult ρ : ℝ) by positivity)
  linarith

/-- **Eliminating `R` when all outside zeros have depth `≤ σ` (`A34` for `σ = 0`).**
When every zero outside `S ∪ S.image reflect` globally satisfies `|ρ.re − ½| ≤ σ` (`0 ≤ σ`,
`δ ≤ ½`, `2 ≤ δa`), taking `R → ∞` internally eliminates the far-tail parameter `R`: specifically,
evaluating at an explicit polynomial-exponential `R` absorbs the far tail into `(1/8) P²`, giving
a pure `e^{2(δ − σ)a} / δ` visibility law with no free auxiliary parameters! -/
theorem windowPositiveAt_global_sea_cluster_bound (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a δ σ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hδa : 2 ≤ δ * a) (hσ : 0 ≤ σ)
    (hpos : WindowPositiveAt Z a)
    (S : Finset ℂ) (hSne : S.Nonempty) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hsea : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) :
    (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) ≤
      120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) *
        Real.log (|γ₀| + 1 / (4 * a) +
          3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a + 6) := by
  have ha4 : 4 ≤ a := by nlinarith
  have ha : 0 < a := by linarith
  have hk1 : 1 ≤ ∑ ρ ∈ S, (Z.mult ρ : ℝ) := by
    obtain ⟨ρ₀, hρ₀⟩ := hSne
    have h1 : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ (hSc ρ₀ hρ₀)
    exact h1.trans (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hρ₀)
  -- Bound `testNorm (sinhTest a δ)` cleanly using `δ ≤ 1/2` and `a ≥ 4`
  have hN_le : testNorm (sinhTest a δ) ≤ 50 * a ^ 6 * Real.exp (δ * a) := by
    have h1 := testNorm_sinhTest_le ha.le hδ.le
    have hcosh : Real.cosh (δ * a) ≤ Real.exp (δ * a) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(δ * a)) ≤ Real.exp (δ * a) :=
        Real.exp_le_exp.mpr (by positivity)
      linarith
    have hpoly : a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3 ≤ 25 * a ^ 5 := by
      have hd2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [pow_nonneg ha.le 3, pow_nonneg ha.le 4]
    calc testNorm (sinhTest a δ)
        ≤ 2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) := h1
      _ ≤ 2 * a * Real.exp (δ * a) * (25 * a ^ 5) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hcosh (by positivity)) hpoly
            (by positivity) (by positivity)
      _ = 50 * a ^ 6 * Real.exp (δ * a) := by ring
  set R := 1 / (4 * a) +
    3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a
  have hR_cone : 1 / (4 * a) ≤ R := by
    dsimp [R]
    have := one_le_log_abs_add_three γ₀
    linarith [show 0 ≤ 3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a by
      positivity]
  have hbound := windowPositiveAt_coherent_cluster_bound Z hA₀ hloc hδ hδa hR_cone hσ hpos
    S hSc hSδ hSγ fun ρ hc hn1 hn2 _ => hsea ρ hc hn1 hn2
  -- Show the far-tail term at this `R` is at most `(1/8) * (a^5 * exp(4δa) / (2^26 * δ^7))`
  have hfar_small :
      384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 * (Real.exp a / (1 + R)) ≤
        (1 / 8) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) := by
    have hL0 : 1 ≤ Real.log (|γ₀| + 3) := one_le_log_abs_add_three γ₀
    have hN2 : testNorm (sinhTest a δ) ^ 2 ≤ 2500 * a ^ 12 * Real.exp (2 * δ * a) := by
      calc testNorm (sinhTest a δ) ^ 2 ≤ (50 * a ^ 6 * Real.exp (δ * a)) ^ 2 :=
            pow_le_pow_left₀ (testNorm_nonneg _) hN_le 2
        _ = 2500 * a ^ 12 * (Real.exp (δ * a) * Real.exp (δ * a)) := by ring
        _ = 2500 * a ^ 12 * Real.exp (2 * δ * a) := by
            rw [← Real.exp_add, show δ * a + δ * a = 2 * δ * a by ring]
    have hd7 : δ ^ 7 ≤ 1 := pow_le_one₀ hδ.le (by linarith)
    have hexp24 : Real.exp (2 * δ * a) ≤ Real.exp (4 * δ * a) :=
      Real.exp_le_exp.mpr (by positivity)
    have h1R_pos : 0 < 1 + R := by linarith [show 0 ≤ 1 / (4 * a) by positivity]
    have hR_big : 3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (2500 * a ^ 7 * δ ^ 7) * Real.exp a ≤
        1 + R := by
      have ha7 : 2500 * a ^ 7 * δ ^ 7 ≤ (50 * a) ^ 7 := by
        calc 2500 * a ^ 7 * δ ^ 7 ≤ 2500 * a ^ 7 * 1 := by gcongr
          _ ≤ 50 ^ 7 * a ^ 7 := by gcongr; norm_num
          _ = (50 * a) ^ 7 := by ring
      dsimp [R]
      have : 3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (2500 * a ^ 7 * δ ^ 7) * Real.exp a ≤
          3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a := by gcongr
      linarith [show 0 ≤ 1 + 1 / (4 * a) by positivity]
    rw [div_eq_mul_inv (Real.exp a) (1 + R), ← mul_assoc, ← mul_assoc]
    rw [show 384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 * Real.exp a * (1 + R)⁻¹ =
        (384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 * Real.exp a) / (1 + R) by
      ring]
    rw [div_le_iff₀ h1R_pos]
    calc 384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 * Real.exp a
        ≤ 384 * A₀ * Real.log (|γ₀| + 3) * (2500 * a ^ 12 * Real.exp (2 * δ * a)) * Real.exp a := by
          gcongr
      _ ≤ 384 * A₀ * Real.log (|γ₀| + 3) * (2500 * a ^ 12 * Real.exp (4 * δ * a)) * Real.exp a := by
          gcongr
      _ = (1 / 8) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) *
            (3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (2500 * a ^ 7 * δ ^ 7) * Real.exp a) := by
          field_simp [hδ.ne']; ring
      _ ≤ (1 / 8) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) * (1 + R) := by
          gcongr
  -- Absorb `(1/8)` into `(5/8) * ∑ m_ρ ≥ (4/8) * ∑ m_ρ + (1/8)` using `1 ≤ ∑ m_ρ`
  have hunit_pos : 0 < a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7) := by positivity
  have hmain : (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) *
      (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) ≤
      4 * A₀ * Real.log (|γ₀| + R + 6) *
        ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
        (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) := by
    nlinarith [mul_le_mul_of_nonneg_right hk1 hunit_pos.le]
  -- Cancel `a^5 * exp(2*(δ + σ)*a) / (2^26 * δ^7)` from both sides
  have hscale : 0 < a ^ 5 * Real.exp (2 * (δ + σ) * a) / (2 ^ 26 * δ ^ 7) := by positivity
  have hlhs : (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) *
      (a ^ 5 * Real.exp (2 * (δ + σ) * a) / (2 ^ 26 * δ ^ 7)) =
      (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) *
        (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) := by
    have hexp_eq : Real.exp (2 * (δ - σ) * a) * Real.exp (2 * (δ + σ) * a) =
        Real.exp (4 * δ * a) := by
      rw [← Real.exp_add]; congr 1; ring
    field_simp [hδ.ne']
    linear_combination (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * a ^ 5 * hexp_eq
  have hrhs : 4 * A₀ * Real.log (|γ₀| + R + 6) *
      ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
      (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) =
      (120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) *
        Real.log (|γ₀| + R + 6)) *
        (a ^ 5 * Real.exp (2 * (δ + σ) * a) / (2 ^ 26 * δ ^ 7)) := by
    have hexp_eq : Real.exp (2 * σ * a) * Real.exp (2 * δ * a) = Real.exp (2 * (δ + σ) * a) := by
      rw [← Real.exp_add]; congr 1; ring
    field_simp [hδ.ne']
    linear_combination 120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) *
      Real.log (|γ₀| + R + 6) * a ^ 5 * hexp_eq
  rw [← hlhs, hrhs] at hmain
  exact le_of_mul_le_mul_right hmain hscale

/-- **Unconditional `ζ` instantiation of coherent-cluster exclusion.** Every positive aperture `a`
with `ZetaWindowPositive a` (in particular every `a ≤ zetaContactAperture` off RH, and
`enlargedWeilFloorAperture` unconditionally!) enforces `windowPositiveAt_coherent_cluster_bound`
with the unconditional Riemann–von Mangoldt constant of `ζ`. -/
theorem zeta_windowPositiveAt_coherent_cluster_bound :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {γ₀ a δ R σ : ℝ}, 0 < δ → 2 ≤ δ * a → 1 / (4 * a) ≤ R → 0 ≤ σ →
        ZetaWindowPositive a →
        ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) →
          (∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) → (∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a)) →
          (∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.im - γ₀| ≤ R →
            |ρ.re - 1 / 2| ≤ σ) →
          (5 / 8) * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) *
              (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) ≤
            4 * A₀ * Real.log (|γ₀| + R + 6) *
              ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) *
              (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) +
            384 * A₀ * Real.log (|γ₀| + 3) * testNorm (sinhTest a δ) ^ 2 *
              (Real.exp a / (1 + R)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun hδ hδa hR hσ hpos S hSc hSδ hSγ hnear =>
    windowPositiveAt_coherent_cluster_bound zetaZeroConfig hA₀ hloc hδ hδa hR hσ
      ((windowPositiveAt_zeta_iff _).mpr hpos) S hSc hSδ hSγ hnear⟩

end GaloisForLFunctions.WindowVisibilityLaw
