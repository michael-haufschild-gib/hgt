import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Visibility law for an isolated off-line pair in a dense on-line background

The background is the doubled on-line lattice `{½ + 2πik/L}`. Into it we insert one reflected
off-line pair `½ ± δ + iγ₀` with `0 < δ ≤ ½`, each point simple.

For tests supported in `[-a, a]` with `a ≤ L/2`, Poisson summation reduces the lattice to its
lag-zero atom `2L‖f‖²`. The pair contributes `2 Re(A conj B)` with
`A = ∫ f(u) e^{iγ₀u} e^{δu} du` and `B = ∫ f(u) e^{iγ₀u} e^{-δu} du`. The rank-two estimate
`2 Re(A conj B) ≥ -½|A - B|² ≥ -2 S(a)‖f‖²`, where
`S(a) = ∫_{-a}^{a} sinh(δu)² du = sinh(2δa)/(2δ) - a`, is sharp: smooth truncations of
`sinh(δu) e^{-iγ₀u}` approach equality. Hence:

* the configuration is Weil-nonnegative at aperture `a ≤ L/2` **iff** `sinh(2δa)/δ ≤ 2L + 2a`;
* it is nonnegative at the Nyquist aperture `L/2` iff `sinh(δL) ≤ 3δL`;
* it is nonnegative at every aperture `a ≤ L/2` with `2δa ≤ log(4δL)`, and becomes negative once
  `2δa ≥ log(4δ(L + a) + 2)`.

Deep pairs (`δL` large) become visible at logarithmic aperture about `log(4δL)/(2δ)`. Shallow pairs
(`sinh(δL) ≤ 3δL`) stay invisible up to `L/2`. The off-line lattice pair has threshold exactly `L/2`
at every depth (`RHTower.offLineLattice_weil_positive_iff`).

For general configurations with a logarithmic local count, `RHTower.IsolatedDeepZeroWeilDetection`
gives a one-sided sufficient condition for negativity. The present law is exact and two-sided in a
background whose density is a free parameter.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 RHTower

/-! ### The configuration -/

/-- The point `½ + δ + iγ₀`. -/
def offLinePoint (δ γ₀ : ℝ) : ℂ := ⟨1 / 2 + δ, γ₀⟩

theorem gammaOf_offLinePoint (δ γ₀ : ℝ) :
    gammaOf (offLinePoint δ γ₀) = (γ₀ : ℂ) - I * δ := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [gammaOf, div_eq_iff Complex.I_ne_zero, offLinePoint, Complex.mk_eq_add_mul_I]
  push_cast
  linear_combination (δ : ℂ) * hI

theorem reflect_offLinePoint (δ γ₀ : ℝ) : reflect (offLinePoint δ γ₀) = offLinePoint (-δ) γ₀ := by
  apply Complex.ext
  · simp only [reflect, offLinePoint, Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  · simp only [reflect, offLinePoint, Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

/-- The doubled on-line lattice of spacing `2π/L` with one inserted reflected off-line pair
`½ ± δ + iγ₀`. On-line points have multiplicity two, the off-line points are simple. -/
def isolatedPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) :
    ZeroConfig where
  carrier := (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀}) ∪
    {offLinePoint (-δ) γ₀}
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ ((⟨k, rfl⟩ | h) | h)
    · simp only [verticalLatticePoint]
      constructor <;> norm_num
    · rw [Set.mem_singleton_iff] at h
      subst h
      simp only [offLinePoint]
      constructor <;> linarith
    · rw [Set.mem_singleton_iff] at h
      subst h
      simp only [offLinePoint]
      constructor <;> linarith
  reflect_mem := by
    rintro _ ((⟨k, rfl⟩ | h) | h)
    · exact Or.inl (Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩)
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Or.inr (by rw [reflect_offLinePoint]; rfl)
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Or.inl (Or.inr (by rw [reflect_offLinePoint, neg_neg]; rfl))
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    refine (((hF.image (verticalLatticePoint L 0)).union
      (Set.finite_singleton (offLinePoint δ γ₀))).union
      (Set.finite_singleton (offLinePoint (-δ) γ₀))).subset ?_
    rintro _ ⟨((⟨k, rfl⟩ | h) | h), h1, h2⟩
    · exact Or.inl (Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-! ### Its Weil form below the Nyquist aperture -/

/-- Below the Nyquist aperture, the on-line lattice part of any configuration that gives lattice
points multiplicity two contributes exactly `2L⟨f, g⟩`. -/
theorem hasSum_Wsummand_onLineLattice (Z : ZeroConfig) {L : ℝ} (hL : 0 < L)
    (hmult : ∀ k : ℤ, Z.mult (verticalLatticePoint L 0 k) = 2) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => Z.Wsummand f g ρ)
      (2 * L * ∫ t, f t * conj (g t)) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hK := EF.weilTest_contDiff hf hg hfc
  have hKs := weilTest_abs_le hfs hgs
  have h0 := tsum_weilTest_lattice_eq hL hf hg hfs hgs
    (fun m : ℤ => (Real.exp (0 * (m * L)) : ℂ)) (by simp)
  have h2 := (hasSum_paperFT_lattice_sub_I_mul hL hK hKs 0).mul_left 2
  rw [h0] at h2
  rw [(verticalLatticePoint_injective hL 0).hasSum_range_iff]
  have hfun : Z.Wsummand f g ∘ verticalLatticePoint L 0 = fun k : ℤ =>
      2 * paperFT (EF.weilTest f g) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ)) := by
    funext k
    rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hg hfc hgc, hmult]
    simp only [Nat.cast_ofNat]
  rw [hfun, show (2 * (L : ℂ) * ∫ t, f t * conj (g t)) =
    2 * ((L : ℂ) * ∫ t, f t * conj (g t)) by ring]
  exact h2

/-- The Weil form of the isolated pair configuration on tests supported in `[-L/2, L/2]`. -/
theorem W_isolatedPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (isolatedPairConfig hL hδ hδ' γ₀).W f f =
      2 * L * (∫ t, f t * conj (f t)) +
        (paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ)) +
          paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ))) := by
  let Z := isolatedPairConfig hL hδ hδ' γ₀
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hmult : ∀ k : ℤ, Z.mult (verticalLatticePoint L 0 k) = 2 := by
    intro k
    rw [hmultdef, if_pos (by simp [verticalLatticePoint])]
  have h₁ := hasSum_Wsummand_onLineLattice Z hL hmult hf hf.continuous hfs hfs
  have hconj₁ : conj ((γ₀ : ℂ) - I * δ) = (γ₀ : ℂ) + I * δ := by
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  have hconj₂ : conj ((γ₀ : ℂ) + I * δ) = (γ₀ : ℂ) - I * δ := by
    simp [map_add, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hvp : Z.Wsummand f f (offLinePoint δ γ₀) =
      paperFT f ((γ₀ : ℂ) - I * δ) * conj (paperFT f ((γ₀ : ℂ) + I * δ)) := by
    have hm : Z.mult (offLinePoint δ γ₀) = 1 := by
      rw [hmultdef, if_neg]
      simp only [offLinePoint]
      linarith
    unfold ZeroConfig.Wsummand
    rw [hm, gammaOf_offLinePoint, hconj₁]
    simp
  have hvq : Z.Wsummand f f (offLinePoint (-δ) γ₀) =
      paperFT f ((γ₀ : ℂ) + I * δ) * conj (paperFT f ((γ₀ : ℂ) - I * δ)) := by
    have hm : Z.mult (offLinePoint (-δ) γ₀) = 1 := by
      rw [hmultdef, if_neg]
      simp only [offLinePoint]
      linarith
    unfold ZeroConfig.Wsummand
    rw [hm, gammaOf_offLinePoint]
    push_cast
    rw [show (γ₀ : ℂ) - I * -(δ : ℂ) = (γ₀ : ℂ) + I * δ by ring, hconj₂]
    simp
  have hp := hasSum_singleton (offLinePoint δ γ₀) (Z.Wsummand f f)
  rw [hvp] at hp
  have hq := hasSum_singleton (offLinePoint (-δ) γ₀) (Z.Wsummand f f)
  rw [hvq] at hq
  have hd₁ : Disjoint (Set.range (verticalLatticePoint L 0)) {offLinePoint δ γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    simp only [verticalLatticePoint, offLinePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀})
      {offLinePoint (-δ) γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨k, hk⟩ | hk)
    · have := congrArg Complex.re hk
      simp only [verticalLatticePoint, offLinePoint] at this
      linarith
    · rw [Set.mem_singleton_iff] at hk
      have := congrArg Complex.re hk
      simp only [offLinePoint] at this
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ h₁ hp) hq
  rw [ZeroConfig.W]
  have heq := hall.tsum_eq
  rw [add_assoc] at heq
  exact heq

/-! ### The rank-two estimate and the energy `S(a)` -/

/-- `S(a) = sinh(2δa)/(2δ) − a`, the integral of `sinh(δu)²` over `[-a, a]`. -/
def pairEnergy (δ a : ℝ) : ℝ := Real.sinh (2 * δ * a) / (2 * δ) - a

theorem integral_sinh_sq_Icc {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ∫ u in Icc (-a) a, Real.sinh (δ * u) ^ 2 = pairEnergy δ a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => Real.sinh (2 * δ * u) / (4 * δ) - u / 2) (Real.sinh (δ * u) ^ 2) u := by
    intro u
    have h1 := ((Real.hasDerivAt_sinh (2 * δ * u)).comp u
      ((hasDerivAt_id u).const_mul (2 * δ))).div_const (4 * δ)
    have h2 := (hasDerivAt_id u).div_const 2
    have hc : Real.cosh (2 * δ * u) = 1 + 2 * Real.sinh (δ * u) ^ 2 := by
      rw [show 2 * δ * u = 2 * (δ * u) by ring, Real.cosh_two_mul, Real.cosh_sq]
      ring
    have hval : Real.cosh (2 * δ * u) * (2 * δ * 1) / (4 * δ) - 1 / 2 =
        Real.sinh (δ * u) ^ 2 := by
      rw [hc]
      field_simp
      ring
    have h3 := h1.sub h2
    rw [hval] at h3
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    ((by fun_prop : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2).intervalIntegrable _ _)]
  simp only [pairEnergy, mul_neg, Real.sinh_neg]
  field_simp
  ring

theorem pairEnergy_nonneg {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) : 0 ≤ pairEnergy δ a := by
  rw [← integral_sinh_sq_Icc hδ ha]
  exact setIntegral_nonneg measurableSet_Icc fun u _ => sq_nonneg _

theorem continuous_pairEnergy (δ : ℝ) : Continuous (pairEnergy δ) := by
  unfold pairEnergy
  fun_prop

/-- The real part of `A conj B + B conj A` is at least `-½|A - B|²`. -/
theorem neg_half_normSq_sub_le_re_pair (A B : ℂ) :
    -(‖A - B‖ ^ 2 / 2) ≤ (A * conj B + B * conj A).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im]
  nlinarith [sq_nonneg (A.re + B.re), sq_nonneg (A.im + B.im)]

theorem integral_mul_conj_self_eq (f : ℝ → ℂ) :
    (∫ t, f t * conj (f t)) = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
  have h : (fun t => f t * conj (f t)) = fun t => ((‖f t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal]

theorem eq_zero_of_not_mem_Icc {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a) {u : ℝ}
    (hu : u ∉ Icc (-a) a) : f u = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hu (hfs h))

/-- **The rank-two pair estimate.** For a test supported in `[-a, a]`,
`|A - B|² ≤ 4 S(a) ‖f‖²`. -/
theorem norm_sub_sq_le_pairEnergy {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (γ₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ‖paperFT f ((γ₀ : ℂ) - I * δ) - paperFT f ((γ₀ : ℂ) + I * δ)‖ ^ 2 ≤
      4 * pairEnergy δ a * ∫ t, ‖f t‖ ^ 2 := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  set w : ℝ → ℝ := fun u => |Real.exp (δ * u) - Real.exp (-δ * u)| with hw
  set g : ℝ → ℝ := (Icc (-a) a).indicator w with hg
  have hdiff : paperFT f ((γ₀ : ℂ) - I * δ) - paperFT f ((γ₀ : ℂ) + I * δ) =
      ∫ u, f u * ((Real.exp (δ * u) - Real.exp (-δ * u) : ℝ) : ℂ) * cexp (I * γ₀ * u) := by
    rw [paperFT_sub_I_mul, paperFT_add_I_mul, paperFT_def, paperFT_def, ← integral_sub]
    · congr 1 with u
      push_cast
      ring
    · exact ((hf.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
        ((hfc.mul_right).mul_right)
    · exact ((hf.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
        ((hfc.mul_right).mul_right)
  have hnorm : ‖paperFT f ((γ₀ : ℂ) - I * δ) - paperFT f ((γ₀ : ℂ) + I * δ)‖ ≤
      ∫ u, ‖f u‖ * g u := by
    rw [hdiff]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun u => ?_)))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (I * (γ₀ : ℂ) * (u : ℂ))‖ = 1 := by
      rw [norm_cexp_I_mul]
      simp
    rw [he, mul_one, hg]
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, eq_zero_of_not_mem_Icc hfs hu]
      simp
  have hgsq : ∀ u, g u ^ 2 = (Icc (-a) a).indicator (fun u => 4 * Real.sinh (δ * u) ^ 2) u := by
    intro u
    by_cases hu : u ∈ Icc (-a) a
    · rw [hg, Set.indicator_of_mem hu, Set.indicator_of_mem hu, hw, sq_abs, Real.sinh_eq]
      rw [show -δ * u = -(δ * u) by ring]
      ring
    · rw [hg, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      ring
  have hfsq : Integrable (fun u => ‖f u‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := -a) (b := a))
      fun u (hu : u ∉ Icc (-a) a) => by simp [eq_zero_of_not_mem_Icc hfs hu])
  have hwc : Continuous w := by rw [hw]; fun_prop
  have hgsq_int : Integrable (fun u => g u ^ 2) := by
    simp_rw [hgsq]
    exact ((by fun_prop : Continuous fun u : ℝ => 4 * Real.sinh (δ * u) ^ 2).integrableOn_Icc
      ).integrable_indicator measurableSet_Icc
  have hgm : AEStronglyMeasurable g :=
    (hwc.aestronglyMeasurable).indicator measurableSet_Icc
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    (hf.norm.aestronglyMeasurable) hgm hfsq hgsq_int
  have hgval : ∫ u, g u ^ 2 = 4 * pairEnergy δ a := by
    simp_rw [hgsq]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_sinh_sq_Icc hδ ha]
  have hprod_nonneg : 0 ≤ ∫ u, ‖f u‖ * g u :=
    integral_nonneg fun u => mul_nonneg (norm_nonneg _)
      (Set.indicator_nonneg (fun _ _ => abs_nonneg _) u)
  calc ‖paperFT f ((γ₀ : ℂ) - I * δ) - paperFT f ((γ₀ : ℂ) + I * δ)‖ ^ 2
      ≤ (∫ u, ‖f u‖ * g u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ u, ‖f u‖ ^ 2) * ∫ u, g u ^ 2 := hcs
    _ = 4 * pairEnergy δ a * ∫ t, ‖f t‖ ^ 2 := by rw [hgval]; ring

/-- **Lower bound below the Nyquist aperture.** For a test supported in `[-a, a]` with
`a ≤ L/2`, `Re W(f, f) ≥ 2(L − S(a))‖f‖²`. -/
theorem re_W_isolatedPairConfig_ge {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * (L - pairEnergy δ a) * ∫ t, ‖f t‖ ^ 2 ≤
      ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith) haL)
  rw [W_isolatedPairConfig hL hδ hδ' γ₀ hf hfs', integral_mul_conj_self_eq]
  have hpair := neg_half_normSq_sub_le_re_pair (paperFT f ((γ₀ : ℂ) - I * δ))
    (paperFT f ((γ₀ : ℂ) + I * δ))
  have hrank := norm_sub_sq_le_pairEnergy hδ ha γ₀ hf.continuous hfs
  have hre : (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 := by
    rw [show (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [Complex.add_re, hre]
  nlinarith

/-! ### The sharp witness -/

/-- Above the threshold `S(a) > L` (and below the Nyquist aperture) a smooth truncation of
`sinh(δu) e^{-iγ₀u}` makes the Weil form negative. -/
theorem exists_re_W_isolatedPairConfig_neg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hS : L < pairEnergy δ a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re < 0 := by
  set S := pairEnergy δ with hSdef
  -- an inner radius `a'` with `S(a')² > L S(a)`
  have hSa : L * S a < S a ^ 2 := by
    have : 0 < S a := hL.trans hS
    nlinarith
  have hev : ∀ᶠ x in 𝓝[<] a, L * S a < S x ^ 2 ∧ a / 2 < x := by
    refine ((((continuous_pairEnergy δ).pow 2).continuousAt.eventually
      (lt_mem_nhds hSa)).and ((continuous_id.continuousAt).eventually
      (lt_mem_nhds (by linarith : a / 2 < a)))).filter_mono nhdsWithin_le_nhds |>.mono ?_
    intro x hx
    exact hx
  obtain ⟨a', ⟨hSa', ha'2⟩, ha'a⟩ := (hev.and self_mem_nhdsWithin).exists
  have ha'pos : 0 < a' := by linarith
  have ha'a : a' < a := ha'a
  set φ : ContDiffBump (0 : ℝ) := ⟨a', a, ha'pos, ha'a⟩ with hφ
  set s : ℝ → ℝ := fun u => Real.sinh (δ * u) * φ u with hs
  set f : ℝ → ℂ := fun u => (s u : ℂ) * cexp (-(I * γ₀ * u)) with hfdef
  have hsc : ContDiff ℝ 2 s := by
    rw [hs]
    exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).mul φ.contDiff
  have hexpc : ContDiff ℝ 2 (fun u : ℝ => cexp (-(I * γ₀ * u))) := by
    have h1 : ContDiff ℝ 2 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp ((contDiff_const.mul h1).neg)
  have hfc2 : ContDiff ℝ 2 f := by
    rw [hfdef]
    exact (Complex.ofRealCLM.contDiff.comp hsc).mul hexpc
  have hsupp_s : ∀ u, u ∉ Icc (-a) a → s u = 0 := by
    intro u hu
    have : φ u = 0 := by
      refine φ.zero_of_le_dist ?_
      rw [Real.dist_eq, sub_zero]
      by_contra hlt
      rw [not_le] at hlt
      exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    simp [hs, this]
  have hfs : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hnot
    exact hu (by simp [hfdef, hsupp_s u hnot])
  refine ⟨f, hfc2, hfs, ?_⟩
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith) haL)
  have hscont : Continuous s := hsc.continuous
  have hscs : HasCompactSupport s := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => hsupp_s u hu
  -- the two tilted transforms are real
  have hA : paperFT f ((γ₀ : ℂ) - I * δ) = ((∫ u, s u * Real.exp (δ * u) : ℝ) : ℂ) := by
    rw [paperFT_sub_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [hfdef]
    have : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (δ * u) : ℂ) * this
  have hB : paperFT f ((γ₀ : ℂ) + I * δ) = ((∫ u, s u * Real.exp (-δ * u) : ℝ) : ℂ) := by
    rw [paperFT_add_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [hfdef]
    have : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (-δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (-δ * u) : ℂ) * this
  set Ap := ∫ u, s u * Real.exp (δ * u) with hAp
  set Bp := ∫ u, s u * Real.exp (-δ * u) with hBp
  set Is := ∫ u, φ u * Real.sinh (δ * u) ^ 2 with hIs
  have hint : ∀ c : ℝ, Integrable (fun u => s u * Real.exp (c * u)) := fun c =>
    (hscont.mul (by fun_prop)).integrable_of_hasCompactSupport hscs.mul_right
  -- parity: `Ap + Bp = 0`
  have hodd : ∫ u, s u * Real.cosh (δ * u) = 0 :=
    RHTower.integral_odd_mul_cosh (fun u => by
      simp only [hs, φ.neg, mul_neg, Real.sinh_neg, neg_mul]) δ
  have hsum : Ap + Bp = 0 := by
    rw [hAp, hBp, ← integral_add (hint δ) (hint (-δ))]
    have h2 : ∫ u, (s u * Real.exp (δ * u) + s u * Real.exp (-δ * u)) =
        2 * ∫ u, s u * Real.cosh (δ * u) := by
      rw [← integral_const_mul]
      congr 1 with u
      rw [Real.cosh_eq, show -δ * u = -(δ * u) by ring]
      ring
    rw [h2, hodd, mul_zero]
  have hsub : Ap - Bp = 2 * Is := by
    rw [hAp, hBp, ← integral_sub (hint δ) (hint (-δ)), hIs, ← integral_const_mul]
    congr 1 with u
    simp only [hs]
    rw [Real.sinh_eq (δ * u), show -δ * u = -(δ * u) by ring]
    ring
  have hApv : Ap = Is := by linarith
  have hBpv : Bp = -Is := by linarith
  -- the energy of the test
  have hnormf : ∀ u, ‖f u‖ ^ 2 = s u ^ 2 := by
    intro u
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, mul_one, sq_abs]
  -- `∫ s² ≤ S(a)` and `Is ≥ S(a')`
  have hupper : ∫ u, ‖f u‖ ^ 2 ≤ S a := by
    simp_rw [hnormf]
    rw [hSdef, ← integral_sinh_sq_Icc hδ ha.le, ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
      (((by fun_prop : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2).integrableOn_Icc
        ).integrable_indicator measurableSet_Icc) (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu]
      simp only [hs, mul_pow]
      have h1 : φ u ^ 2 ≤ 1 := by
        have := φ.le_one (x := u); have := φ.nonneg (x := u); nlinarith
      nlinarith [sq_nonneg (Real.sinh (δ * u))]
    · rw [Set.indicator_of_notMem hu, hsupp_s u hu]
      norm_num
  have hlower : S a' ≤ Is := by
    rw [hSdef, ← integral_sinh_sq_Icc hδ ha'pos.le, ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_)
      ((φ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.mul_right)) (Eventually.of_forall fun u => ?_)
    · exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) u
    · dsimp only
      by_cases hu : u ∈ Icc (-a') a'
      · rw [Set.indicator_of_mem hu, φ.one_of_mem_closedBall]
        · ring_nf; exact le_rfl
        · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
          exact ⟨hu.1, hu.2⟩
      · rw [Set.indicator_of_notMem hu]
        exact mul_nonneg φ.nonneg (sq_nonneg _)
  have hSa'0 : 0 ≤ S a' := pairEnergy_nonneg hδ ha'pos.le
  -- assemble
  rw [W_isolatedPairConfig hL hδ hδ' γ₀ hfc2 hfs', integral_mul_conj_self_eq, hA, hB,
    hApv, hBpv]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  have hIs2 : S a' ^ 2 ≤ Is ^ 2 := pow_le_pow_left₀ hSa'0 hlower 2
  nlinarith [hupper, hIs2, hSa']

/-! ### The visibility law -/

/-- **Exact visibility law below the Nyquist aperture.** For `0 < a ≤ L/2`, the isolated pair
configuration is Weil-nonnegative on all `C²` tests supported in `[-a, a]` iff
`sinh(2δa)/δ ≤ 2L + 2a`. -/
theorem isolatedPairConfig_weil_nonneg_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re) ↔
      Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a := by
  have hiff : Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a ↔ pairEnergy δ a ≤ L := by
    unfold pairEnergy
    rw [div_le_iff₀ hδ, sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
    constructor <;> intro h <;> linarith
  rw [hiff]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨f, hf, hfs, hneg⟩ := exists_re_W_isolatedPairConfig_neg hL hδ hδ' γ₀ ha haL hlt
    exact absurd (h f hf hfs) (not_le.mpr hneg)
  · intro h f hf hfs
    have := re_W_isolatedPairConfig_ge hL hδ hδ' γ₀ ha.le haL hf hfs
    have hn : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith

/-- **Visibility at the Nyquist aperture.** The isolated pair is invisible on `[-L/2, L/2]` iff
`sinh(δL) ≤ 3δL`. -/
theorem isolatedPairConfig_weil_nonneg_nyquist_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(L / 2)) (L / 2) →
      0 ≤ ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re) ↔
      Real.sinh (δ * L) ≤ 3 * δ * L := by
  rw [isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ (by linarith) le_rfl,
    show 2 * δ * (L / 2) = δ * L by ring, div_le_iff₀ hδ]
  constructor <;> intro h <;> nlinarith

/-- **Invisibility below the logarithmic aperture.** If `2δa ≤ log(4δL)` (and `a ≤ L/2`), the
isolated pair is invisible at aperture `a`. -/
theorem isolatedPairConfig_weil_nonneg_of_le_log {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hlog : 2 * δ * a ≤ Real.log (4 * δ * L)) :
    ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re := by
  rw [isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL, div_le_iff₀ hδ]
  have hexp : Real.exp (2 * δ * a) ≤ 4 * δ * L := by
    calc Real.exp (2 * δ * a) ≤ Real.exp (Real.log (4 * δ * L)) := Real.exp_le_exp.mpr hlog
      _ = 4 * δ * L := Real.exp_log (by positivity)
  have hsinh : Real.sinh (2 * δ * a) ≤ Real.exp (2 * δ * a) / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(2 * δ * a))
    linarith
  nlinarith

/-- **Visibility above the logarithmic aperture.** If `log(4δ(L + a) + 2) ≤ 2δa` (and
`a ≤ L/2`), some `C²` test supported in `[-a, a]` makes the Weil form negative. -/
theorem exists_re_W_isolatedPairConfig_neg_of_log_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hlog : Real.log (4 * δ * (L + a) + 2) ≤ 2 * δ * a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((isolatedPairConfig hL hδ hδ' γ₀).W f f).re < 0 := by
  have hnot : ¬ (Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a) := by
    rw [div_le_iff₀ hδ, not_le]
    have hexp : 4 * δ * (L + a) + 2 ≤ Real.exp (2 * δ * a) := by
      calc 4 * δ * (L + a) + 2 = Real.exp (Real.log (4 * δ * (L + a) + 2)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (2 * δ * a) := Real.exp_le_exp.mpr hlog
    have hsmall : Real.exp (-(2 * δ * a)) < 1 := by
      have : 0 < 2 * δ * a := by positivity
      have h := Real.exp_lt_exp.mpr (show -(2 * δ * a) < 0 by linarith)
      rwa [Real.exp_zero] at h
    rw [Real.sinh_eq]
    nlinarith
  rw [← isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL] at hnot
  simp only [not_forall, not_le, exists_prop] at hnot
  obtain ⟨f, hf, hfs, hneg⟩ := hnot
  exact ⟨f, hf, hfs, hneg⟩

end GaloisForLFunctions.SquareRootThreshold
