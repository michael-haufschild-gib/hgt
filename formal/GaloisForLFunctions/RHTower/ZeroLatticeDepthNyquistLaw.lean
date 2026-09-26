import Zeta23.Poisson
import Zeta23.ExplicitFormula

/-!
# The Nyquist law for the depth of a vertical zero lattice

Zeta23's Weil form `W(f, g) = Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))` is evaluated on two abstract
zero configurations with ordinate spacing `2π/L`:

* the doubled on-line lattice `{½ + 2πik/L}`, each point of multiplicity two;
* the off-line lattice pair `{½ ± δ + 2πik/L}`, `0 < δ ≤ ½`, each point simple.

A vertical shift `∓iδ` of the Fourier variable is the exponential tilt `e^{±δu}` of the test
kernel, and Poisson summation over the ordinate lattice turns the zero sum into the lag sum
`L Σ_m k(mL)(e^{δmL} + e^{-δmL})` of the Weil kernel `k = f ⋆ g̃`.

* **Blindness.**  For tests supported in `[-L/2, L/2]` the kernel `k` is supported in `[-L, L]` and
  vanishes at `±L`, only the lag-zero atom survives, and both configurations have Weil form
  `2L⟨f, g⟩`, whatever the depth.
* **Detection.**  For every level `a > L/2` a difference of two bumps at distance `L` has Weil
  kernel atoms `2B, -B, -B` at the lags `0, ±L`, and the off-line form equals
  `-2LB(e^{δL/2} - e^{-δL/2})² < 0`.
* **On-line positivity.**  The doubled on-line lattice has nonnegative Weil form at every level.

Hence the off-line lattice pair passes the level-`a` Weil positivity test exactly when
`a ≤ L/2`, that is when the level is at most `π` over the ordinate spacing.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- Poisson summation on the ordinate lattice `(2π/L)ℤ` for a compactly supported `C²`
function: `Σ_k ĉ(2πk/L) = L Σ_m c(mL)`. -/
theorem hasSum_paperFT_lattice {c : ℝ → ℂ} {A L : ℝ} (hL : 0 < L)
    (hc : ContDiff ℝ 2 c) (hsupp : ∀ u, c u ≠ 0 → |u| ≤ A) :
    HasSum (fun k : ℤ => paperFT c ((k : ℝ) * (2 * π / L) : ℝ)) (L * ∑' m : ℤ, c (m * L)) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcs : HasCompactSupport c := hasCompactSupport_of_support_subset_abs hsupp
  have hcc : Continuous c := hc.continuous
  set G : ℝ → ℂ := fun x => (L : ℂ) * c (L * x) with hG
  have hGc : Continuous G := continuous_const.mul (hcc.comp (continuous_const.mul continuous_id))
  have hGz : ∀ x : ℝ, A / L + 1 ≤ |x| → G x = 0 := by
    intro x hx
    have h1 : c (L * x) = 0 := by
      by_contra hne
      have h2 := hsupp _ hne
      rw [abs_mul, abs_of_pos hL] at h2
      have hLx : L * (A / L + 1) ≤ L * |x| := mul_le_mul_of_nonneg_left hx hL.le
      rw [mul_add, mul_div_cancel₀ _ hL.ne', mul_one] at hLx
      linarith
    simp [hG, h1]
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, A / L + 1 ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hGz x (by simpa using hx)]
    simp
  -- the Fourier transform of G is a sample of `paperFT c`
  have hFG : ∀ w : ℝ, 𝓕 G w = paperFT c ((-(w * (2 * π / L)) : ℝ) : ℂ) := by
    intro w
    rw [fourier_eq_paperFT, paperFT_def, paperFT_def]
    have hscale := Measure.integral_comp_mul_left
      (fun u : ℝ => c u * cexp (I * ((-(w * (2 * π / L)) : ℝ) : ℂ) * (u : ℂ))) L
    rw [abs_of_pos (inv_pos.mpr hL)] at hscale
    have hint : (∫ u : ℝ, G u * cexp (I * ((-(2 * π * w) : ℝ) : ℂ) * (u : ℂ))) =
        (L : ℂ) * ∫ u : ℝ, c (L * u) *
          cexp (I * ((-(w * (2 * π / L)) : ℝ) : ℂ) * ((L * u : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      congr 1 with u
      have hexp : I * ((-(w * (2 * π / L)) : ℝ) : ℂ) * ((L * u : ℝ) : ℂ) =
          I * ((-(2 * π * w)) : ℝ) * (u : ℂ) := by
        push_cast
        field_simp
      simp only [hG]
      rw [hexp]
      ring
    have e2 : ((-(2 * π * w) : ℝ) : ℂ) = -(2 * (π : ℂ) * w) := by push_cast; ring
    rw [e2] at hint
    rw [hint, hscale, Complex.real_smul, ← mul_assoc]
    push_cast
    field_simp
  -- decay of the Fourier transform
  obtain ⟨C, hC⟩ : ∃ C, ∀ s : ℝ, ‖paperFT c s‖ * (1 + s ^ 2) ≤ C := by
    refine ⟨(∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖, fun s => ?_⟩
    have h0 := norm_paperFT_le (hcc.integrable_of_hasCompactSupport hcs) hsupp (s : ℂ)
    have h2 := norm_paperFT_mul_sq_le hc hsupp (s : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] at h0 h2
    nlinarith [norm_nonneg (paperFT c s)]
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply Poisson.isBigO_of_decay (c := 0) (h := 2 * π / L) (C := C) (by positivity)
    intro w
    rw [hFG w]
    have := hC (-(w * (2 * π / L)))
    have e : (0 - w * (2 * π / L)) ^ 2 = (-(w * (2 * π / L))) ^ 2 := by ring
    rw [e]
    exact this
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = L * ∑' m : ℤ, c (m * L) := by
    simp only [hG, zero_add]
    rw [tsum_mul_left]
    congr 1
    exact tsum_congr fun m => by rw [mul_comm]
  have rhs : ∑' n : ℤ, 𝓕 G n * fourier n ((0 : ℝ) : UnitAddCircle) = ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  have hs : HasSum (fun n : ℤ => 𝓕 G n) (L * ∑' m : ℤ, c (m * L)) := by
    rw [key]; exact hsum.hasSum
  -- reindex `n ↦ -n`
  have hs' := (Equiv.neg ℤ).hasSum_iff.mpr hs
  convert hs' using 1
  funext k
  simp only [Function.comp_apply, Equiv.neg_apply, hFG]
  push_cast
  ring_nf

/-- A vertical shift of the Fourier variable is an exponential tilt of the test function. -/
theorem paperFT_sub_I_mul (K : ℝ → ℂ) (s δ : ℝ) :
    paperFT K ((s : ℂ) - I * δ) = paperFT (fun u => K u * (Real.exp (δ * u) : ℂ)) s := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  have he : cexp (I * ((s : ℂ) - I * δ) * u) =
      (Real.exp (δ * u) : ℂ) * cexp (I * s * u) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(δ : ℂ) * u) * hI
  rw [he]
  ring

theorem paperFT_add_I_mul (K : ℝ → ℂ) (s δ : ℝ) :
    paperFT K ((s : ℂ) + I * δ) = paperFT (fun u => K u * (Real.exp (-δ * u) : ℂ)) s := by
  have := paperFT_sub_I_mul K s (-δ)
  rw [show (s : ℂ) - I * ((-δ : ℝ) : ℂ) = (s : ℂ) + I * δ by push_cast; ring] at this
  exact this

private theorem contDiff_tilt {K : ℝ → ℂ} (hK : ContDiff ℝ 2 K) (δ : ℝ) :
    ContDiff ℝ 2 (fun u => K u * (Real.exp (δ * u) : ℂ)) := by
  apply hK.mul
  have : ContDiff ℝ 2 (fun u : ℝ => Real.exp (δ * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  exact Complex.ofRealCLM.contDiff.comp this

/-- Tilted Poisson summation: a vertical shift `-iδ` of the lattice multiplies the lag-`mL`
atom by `e^{δmL}`. -/
theorem hasSum_paperFT_lattice_sub_I_mul {K : ℝ → ℂ} {A L : ℝ} (hL : 0 < L)
    (hK : ContDiff ℝ 2 K) (hsupp : ∀ u, K u ≠ 0 → |u| ≤ A) (δ : ℝ) :
    HasSum (fun k : ℤ => paperFT K (((k : ℝ) * (2 * π / L) : ℝ) - I * δ))
      (L * ∑' m : ℤ, K (m * L) * (Real.exp (δ * (m * L)) : ℂ)) := by
  have hsp : ∀ u, K u * (Real.exp (δ * u) : ℂ) ≠ 0 → |u| ≤ A := fun u hu =>
    hsupp u (fun h0 => hu (by rw [h0, zero_mul]))
  convert hasSum_paperFT_lattice hL (contDiff_tilt hK δ) hsp using 1
  funext k
  rw [paperFT_sub_I_mul]

/-! ### Vertical zero lattices as abstract zero configurations -/

/-- The point `½ + δ + i·k(2π/L)` of the vertical lattice with abscissa `½ + δ` and ordinate
spacing `2π/L`. -/
def verticalLatticePoint (L δ : ℝ) (k : ℤ) : ℂ := ⟨1 / 2 + δ, (k : ℝ) * (2 * π / L)⟩

theorem gammaOf_verticalLatticePoint (L δ : ℝ) (k : ℤ) :
    gammaOf (verticalLatticePoint L δ k) = (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * δ := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [gammaOf, div_eq_iff Complex.I_ne_zero, verticalLatticePoint, Complex.mk_eq_add_mul_I]
  push_cast
  linear_combination (δ : ℂ) * hI

theorem reflect_verticalLatticePoint (L δ : ℝ) (k : ℤ) :
    reflect (verticalLatticePoint L δ k) = verticalLatticePoint L (-δ) k := by
  apply Complex.ext
  · simp only [reflect, verticalLatticePoint, Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  · simp only [reflect, verticalLatticePoint, Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

theorem verticalLatticePoint_injective {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    Function.Injective (verticalLatticePoint L δ) := by
  intro k k' h
  have him := congrArg Complex.im h
  simp only [verticalLatticePoint] at him
  have hh : (2 * π / L) ≠ 0 := by positivity
  exact_mod_cast mul_right_cancel₀ hh him

theorem finite_latticeWindow {h : ℝ} (hh : 0 < h) (T₁ T₂ : ℝ) :
    {k : ℤ | T₁ < (k : ℝ) * h ∧ (k : ℝ) * h ≤ T₂}.Finite := by
  apply (Set.finite_Icc ⌊T₁ / h⌋ ⌈T₂ / h⌉).subset
  rintro k ⟨h1, h2⟩
  have h1' : T₁ / h < k := by rwa [div_lt_iff₀ hh]
  have h2' : (k : ℝ) ≤ T₂ / h := by rwa [le_div_iff₀ hh]
  have h3 : (⌊T₁ / h⌋ : ℝ) < k := (Int.floor_le _).trans_lt h1'
  have h4 : (k : ℝ) ≤ ⌈T₂ / h⌉ := h2'.trans (Int.le_ceil _)
  exact ⟨(by exact_mod_cast h3 : ⌊T₁ / h⌋ < k).le, by exact_mod_cast h4⟩

/-- The doubled on-line lattice `{½ + 2πik/L}`, every point of multiplicity two. -/
def onLineLatticeConfig {L : ℝ} (hL : 0 < L) : ZeroConfig where
  carrier := Set.range (verticalLatticePoint L 0)
  mult := fun _ => 2
  one_le_mult := fun _ _ => by norm_num
  strip := by
    rintro _ ⟨k, rfl⟩
    simp only [verticalLatticePoint]
    norm_num
  reflect_mem := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    refine ((finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂).image
      (verticalLatticePoint L 0)).subset ?_
    rintro _ ⟨⟨k, rfl⟩, h1, h2⟩
    exact ⟨k, ⟨h1, h2⟩, rfl⟩

/-- The off-line lattice pair `{½ ± δ + 2πik/L}`, every point simple. -/
def offLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ZeroConfig where
  carrier := Set.range (verticalLatticePoint L δ) ∪ Set.range (verticalLatticePoint L (-δ))
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp only [verticalLatticePoint] <;> constructor <;>
      linarith
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inr ⟨k, (reflect_verticalLatticePoint L δ k).symm⟩
    · exact Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_neg]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    refine ((hF.image (verticalLatticePoint L δ)).union
      (hF.image (verticalLatticePoint L (-δ)))).subset ?_
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩

/-! ### The Weil form of a vertical lattice -/

theorem Wsummand_verticalLatticePoint (Z : ZeroConfig) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (L δ : ℝ)
    (k : ℤ) :
    Z.Wsummand f g (verticalLatticePoint L δ k) = (Z.mult (verticalLatticePoint L δ k) : ℂ) *
      paperFT (EF.weilTest f g) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * δ) := by
  rw [ZeroConfig.Wsummand, EF.paperFT_weilTest hf hg hfs hgs, gammaOf_verticalLatticePoint,
    mul_assoc]

theorem hasCompactSupport_of_tsupport_subset_Icc {f : ℝ → ℂ} {A : ℝ}
    (h : tsupport f ⊆ Icc (-A) A) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) h

theorem weilTest_abs_le {f g : ℝ → ℂ} {A : ℝ}
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) (hgs : tsupport g ⊆ Icc (-(A / 2)) (A / 2)) :
    ∀ u, EF.weilTest f g u ≠ 0 → |u| ≤ A := fun _ hu =>
  abs_le.mpr (EF.tsupport_weilTest_subset hfs hgs (subset_tsupport _ hu))

theorem weilTest_apply (f g : ℝ → ℂ) (x : ℝ) :
    EF.weilTest f g x = ∫ t, f t * conj (g (t - x)) := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]

/-- Weil form of the off-line lattice pair: the lag-`mL` atoms of `k = f ⋆ g̃`, weighted by
`e^{δmL} + e^{-δmL}`. -/
theorem W_offLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {f g : ℝ → ℂ} {A : ℝ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) (hgs : tsupport g ⊆ Icc (-(A / 2)) (A / 2)) :
    (offLineLatticeConfig hL hδ hδ').W f g =
      L * ∑' m : ℤ, EF.weilTest f g (m * L) * (Real.exp (δ * (m * L)) : ℂ) +
        L * ∑' m : ℤ, EF.weilTest f g (m * L) * (Real.exp (-δ * (m * L)) : ℂ) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hK := EF.weilTest_contDiff hf hg hfc
  have hKs := weilTest_abs_le hfs hgs
  have hdisj : Disjoint (Set.range (verticalLatticePoint L δ))
      (Set.range (verticalLatticePoint L (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith
  have h₁ : HasSum (fun ρ : Set.range (verticalLatticePoint L δ) =>
      (offLineLatticeConfig hL hδ hδ').Wsummand f g ρ)
      (L * ∑' m : ℤ, EF.weilTest f g (m * L) * (Real.exp (δ * (m * L)) : ℂ)) := by
    rw [(verticalLatticePoint_injective hL δ).hasSum_range_iff]
    convert hasSum_paperFT_lattice_sub_I_mul hL hK hKs δ using 1
    funext k
    rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hg hfc hgc]
    simp [offLineLatticeConfig]
  have h₂ : HasSum (fun ρ : Set.range (verticalLatticePoint L (-δ)) =>
      (offLineLatticeConfig hL hδ hδ').Wsummand f g ρ)
      (L * ∑' m : ℤ, EF.weilTest f g (m * L) * (Real.exp (-δ * (m * L)) : ℂ)) := by
    rw [(verticalLatticePoint_injective hL (-δ)).hasSum_range_iff]
    convert hasSum_paperFT_lattice_sub_I_mul hL hK hKs (-δ) using 1
    funext k
    rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hg hfc hgc]
    simp [offLineLatticeConfig]
  rw [ZeroConfig.W]
  exact (HasSum.add_disjoint (f := (offLineLatticeConfig hL hδ hδ').Wsummand f g)
    hdisj h₁ h₂).tsum_eq

/-- Weil form of the doubled on-line lattice. -/
theorem W_onLineLatticeConfig {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ} {A : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) (hgs : tsupport g ⊆ Icc (-(A / 2)) (A / 2)) :
    (onLineLatticeConfig hL).W f g = 2 * (L * ∑' m : ℤ, EF.weilTest f g (m * L)) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hK := EF.weilTest_contDiff hf hg hfc
  have hKs := weilTest_abs_le hfs hgs
  have h : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) =>
      (onLineLatticeConfig hL).Wsummand f g ρ)
      (2 * (L * ∑' m : ℤ, EF.weilTest f g (m * L))) := by
    have h0 : ∑' m : ℤ, EF.weilTest f g (m * L) * (Real.exp (0 * (m * L)) : ℂ) =
        ∑' m : ℤ, EF.weilTest f g (m * L) := by simp
    have h2 : HasSum (fun k : ℤ => (2 : ℂ) *
        paperFT (EF.weilTest f g) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ)))
        (2 * (L * ∑' m : ℤ, EF.weilTest f g (m * L))) := by
      rw [← h0]
      exact (hasSum_paperFT_lattice_sub_I_mul hL hK hKs 0).mul_left 2
    rw [(verticalLatticePoint_injective hL 0).hasSum_range_iff]
    convert h2 using 1
    funext k
    rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hg hfc hgc]
    simp [onLineLatticeConfig]
  rw [ZeroConfig.W]
  exact h.tsum_eq

/-- The doubled on-line lattice passes the Weil positivity test at every level. -/
theorem re_W_onLineLatticeConfig_nonneg {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) :
    0 ≤ ((onLineLatticeConfig hL).W f f).re := by
  have hterm : ∀ ρ : (onLineLatticeConfig hL).carrier,
      (onLineLatticeConfig hL).Wsummand f f ρ =
        ((2 * Complex.normSq (paperFT f (gammaOf ρ)) : ℝ) : ℂ) := by
    rintro ⟨_, k, rfl⟩
    have hc : conj (gammaOf (verticalLatticePoint L 0 k)) = gammaOf (verticalLatticePoint L 0 k) := by
      rw [gammaOf_verticalLatticePoint, Complex.ofReal_zero, mul_zero, sub_zero,
        Complex.conj_ofReal]
    simp only [ZeroConfig.Wsummand, hc, onLineLatticeConfig]
    rw [mul_assoc, Complex.mul_conj]
    push_cast
    ring
  rw [ZeroConfig.W, tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun ρ => mul_nonneg zero_le_two (Complex.normSq_nonneg _)

/-! ### Below the Nyquist level the Weil form is blind to depth -/

theorem eq_zero_of_tsupport_subset_Icc {K : ℝ → ℂ} {A u : ℝ} (hK : Continuous K)
    (hKs : tsupport K ⊆ Icc (-A) A) (hu : A ≤ |u|) : K u = 0 := by
  by_contra hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_support u hne
  rcases le_or_gt 0 u with h0 | h0
  · have hv : u + ε / 2 ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, Real.dist_eq, show u + ε / 2 - u = ε / 2 by ring,
        abs_of_pos (by linarith)]
      linarith
    have := hKs (subset_tsupport _ (hball hv))
    rw [abs_of_nonneg h0] at hu
    linarith [this.2]
  · have hv : u - ε / 2 ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, Real.dist_eq, show u - ε / 2 - u = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    have := hKs (subset_tsupport _ (hball hv))
    rw [abs_of_neg h0] at hu
    linarith [this.1]

theorem tsum_weilTest_lattice_eq {f g : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2))
    (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) (φ : ℤ → ℂ) (hφ : φ 0 = 1) :
    ∑' m : ℤ, EF.weilTest f g (m * L) * φ m = ∫ t, f t * conj (g t) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hKc := (EF.weilTest_contDiff hf hg hfc).continuous
  have hKs := EF.tsupport_weilTest_subset hfs hgs
  rw [tsum_eq_single 0]
  · simp [hφ, weilTest_apply]
  · intro m hm
    rw [eq_zero_of_tsupport_subset_Icc hKc hKs, zero_mul]
    rw [abs_mul, abs_of_pos hL]
    have : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hm
    nlinarith

/-- **Depth-blindness below the Nyquist level.**  For test functions supported in
`[-L/2, L/2]`, the off-line lattice pair `{½ ± δ + 2πik/L}` has Weil form `2L⟨f, g⟩`,
independent of the depth `δ`. -/
theorem W_offLineLatticeConfig_of_le_nyquist {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    (offLineLatticeConfig hL hδ hδ').W f g = 2 * L * ∫ t, f t * conj (g t) := by
  rw [W_offLineLatticeConfig hL hδ hδ' hf hg hfs hgs,
    tsum_weilTest_lattice_eq hL hf hg hfs hgs (fun m : ℤ => (Real.exp (δ * (m * L)) : ℂ))
      (by simp),
    tsum_weilTest_lattice_eq hL hf hg hfs hgs (fun m : ℤ => (Real.exp (-δ * (m * L)) : ℂ))
      (by simp)]
  ring

theorem W_onLineLatticeConfig_of_le_nyquist {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    (onLineLatticeConfig hL).W f g = 2 * L * ∫ t, f t * conj (g t) := by
  have h := tsum_weilTest_lattice_eq hL hf hg hfs hgs (fun _ => 1) rfl
  simp only [mul_one] at h
  rw [W_onLineLatticeConfig hL hf hg hfs hgs, h]
  ring

/-- The off-line lattice pair and the doubled on-line lattice have the same Weil form on
`L²(-L/2, L/2)`. -/
theorem W_offLineLatticeConfig_eq_onLine {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    (offLineLatticeConfig hL hδ hδ').W f g = (onLineLatticeConfig hL).W f g := by
  rw [W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf hg hfs hgs,
    W_onLineLatticeConfig_of_le_nyquist hL hf hg hfs hgs]

theorem re_integral_mul_conj_self_nonneg (f : ℝ → ℂ) :
    0 ≤ (∫ t, f t * conj (f t)).re := by
  have h : (fun t => f t * conj (f t)) = fun t => ((Complex.normSq (f t) : ℝ) : ℂ) := by
    funext t
    rw [Complex.mul_conj]
  rw [h, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun t => Complex.normSq_nonneg _

/-! ### Above the Nyquist level the Weil form detects every depth -/

/-- **Depth detection above the Nyquist level.**  For every level `a > L/2` and every depth
`δ ∈ (0, ½]`, a smooth test function supported in `[-a, a]` makes the Weil form of the off-line
lattice pair negative.  The test is a difference of two bumps at distance `L`, whose Weil kernel
has atoms `2B, -B, -B` at the lags `0, ±L`; the form equals `-2LB(e^{δL/2} - e^{-δL/2})²`. -/
theorem exists_re_W_offLineLatticeConfig_neg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((offLineLatticeConfig hL hδ hδ').W f f).re < 0 := by
  set ε : ℝ := min (a - L / 2) (L / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
  have hεa : L / 2 + ε ≤ a := by
    have := min_le_left (a - L / 2) (L / 2); rw [hε]; linarith
  have hεL : ε < L / 2 := by
    have := min_le_right (a - L / 2) (L / 2); rw [hε]; linarith
  obtain ⟨b, hbr⟩ : ∃ b : ContDiffBump (0 : ℝ), b.rOut = ε :=
    ⟨⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩, rfl⟩
  set β : ℝ → ℝ := ⇑b with hβdef
  have hβs : ∀ x, β x ≠ 0 → |x| < ε := by
    intro x hx
    have hx' : x ∈ Function.support β := hx
    rw [hβdef, b.support_eq, hbr, Metric.mem_ball, Real.dist_eq, sub_zero] at hx'
    exact hx'
  have hβd : ∀ x y, 2 * ε ≤ |x - y| → β x * β y = 0 := by
    intro x y hxy
    by_contra hne
    have hx := abs_lt.mp (hβs x (left_ne_zero_of_mul hne))
    have hy := abs_lt.mp (hβs y (right_ne_zero_of_mul hne))
    have : |x - y| < 2 * ε := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have hβi : Integrable (fun x => β x * β x) :=
    (b.continuous.mul b.continuous).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  set B : ℝ := ∫ x, β x * β x with hBdef
  have hB : 0 < B := by
    rw [hBdef, integral_pos_iff_support_of_nonneg (fun x => mul_self_nonneg (β x)) hβi,
      Function.support_mul, Set.inter_self, hβdef, b.support_eq, hbr]
    exact Metric.measure_ball_pos volume 0 hε0
  set F : ℝ → ℝ := fun t => β (t + L / 2) - β (t - L / 2) with hF
  have hFs : ∀ t, F t ≠ 0 → |t| < L / 2 + ε := by
    intro t ht
    by_cases h1 : β (t + L / 2) = 0
    · have h2 : β (t - L / 2) ≠ 0 := by
        intro h2; apply ht; simp only [hF, h1, h2, sub_zero]
      have := abs_lt.mp (hβs _ h2)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have := abs_lt.mp (hβs _ h1)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  set f : ℝ → ℂ := fun t => (F t : ℂ) with hf
  have hb2 : ContDiff ℝ 2 β := b.contDiff
  have hFc : ContDiff ℝ 2 F :=
    (hb2.comp (contDiff_id.add contDiff_const)).sub (hb2.comp (contDiff_id.sub contDiff_const))
  have hfc : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hFc
  have hfs : tsupport f ⊆ Icc (-(L / 2 + ε)) (L / 2 + ε) := by
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have ht' : F t ≠ 0 := fun h => ht (by simp [hf, h])
    exact abs_le.mp (hFs t ht').le
  refine ⟨f, hfc, hfs.trans (Icc_subset_Icc (by linarith) hεa), ?_⟩
  -- the Weil kernel of `f` is real
  have hK : ∀ x, EF.weilTest f f x = ((∫ t, F t * F (t - x) : ℝ) : ℂ) := by
    intro x
    rw [weilTest_apply, ← integral_complex_ofReal]
    congr 1 with t
    simp [hf, Complex.conj_ofReal]
  have hRzero : ∀ x, 2 * L ≤ |x| → ∫ t, F t * F (t - x) = 0 := by
    intro x hx
    have : (fun t => F t * F (t - x)) = fun _ => 0 := by
      funext t
      by_contra hne
      have h1 := abs_lt.mp (hFs t (left_ne_zero_of_mul hne))
      have h2 := abs_lt.mp (hFs _ (right_ne_zero_of_mul hne))
      have : |x| < 2 * L := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [this, integral_zero]
  have hK0 : EF.weilTest f f 0 = ((2 * B : ℝ) : ℂ) := by
    rw [hK]
    congr 1
    have hpt : ∀ t, F t * F (t - 0) =
        β (t + L / 2) * β (t + L / 2) + β (t - L / 2) * β (t - L / 2) := by
      intro t
      have := hβd (t + L / 2) (t - L / 2) (by
        rw [show t + L / 2 - (t - L / 2) = L by ring, abs_of_pos hL]; linarith)
      simp only [hF, sub_zero]
      linear_combination (-2) * this
    simp_rw [hpt]
    rw [integral_add (hβi.comp_add_right (L / 2)) (hβi.comp_sub_right (L / 2)),
      integral_add_right_eq_self (fun x => β x * β x), integral_sub_right_eq_self
        (fun x => β x * β x)]
    ring
  have hKp : EF.weilTest f f L = ((-B : ℝ) : ℂ) := by
    rw [hK]
    congr 1
    have hpt : ∀ t, F t * F (t - L) = -(β (t - L / 2) * β (t - L / 2)) := by
      intro t
      have e : t - L + L / 2 = t - L / 2 := by ring
      have h1 := hβd (t + L / 2) (t - L / 2) (by
        rw [show t + L / 2 - (t - L / 2) = L by ring, abs_of_pos hL]; linarith)
      have h2 := hβd (t + L / 2) (t - L - L / 2) (by
        rw [show t + L / 2 - (t - L - L / 2) = 2 * L by ring, abs_of_pos (by linarith)]
        linarith)
      have h3 := hβd (t - L / 2) (t - L - L / 2) (by
        rw [show t - L / 2 - (t - L - L / 2) = L by ring, abs_of_pos hL]; linarith)
      simp only [hF]
      rw [e]
      linear_combination h1 - h2 + h3
    simp_rw [hpt]
    rw [integral_neg, integral_sub_right_eq_self (fun x => β x * β x)]
  have hKm : EF.weilTest f f (-L) = ((-B : ℝ) : ℂ) := by
    rw [hK]
    congr 1
    have hpt : ∀ t, F t * F (t - -L) = -(β (t + L / 2) * β (t + L / 2)) := by
      intro t
      have e : t - -L - L / 2 = t + L / 2 := by ring
      have h1 := hβd (t + L / 2) (t - -L + L / 2) (by
        rw [show t + L / 2 - (t - -L + L / 2) = -L by ring, abs_neg, abs_of_pos hL]; linarith)
      have h2 := hβd (t - L / 2) (t - -L + L / 2) (by
        rw [show t - L / 2 - (t - -L + L / 2) = -(2 * L) by ring, abs_neg,
          abs_of_pos (by linarith)]
        linarith)
      have h3 := hβd (t - L / 2) (t + L / 2) (by
        rw [show t - L / 2 - (t + L / 2) = -L by ring, abs_neg, abs_of_pos hL]; linarith)
      simp only [hF]
      rw [e]
      linear_combination h1 - h2 + h3
    simp_rw [hpt]
    rw [integral_neg, integral_add_right_eq_self (fun x => β x * β x)]
  -- only the lags `0, ±L` survive
  have hvan : ∀ φ : ℤ → ℂ, ∀ m ∉ ({-1, 0, 1} : Finset ℤ),
      EF.weilTest f f (m * L) * φ m = 0 := by
    intro φ m hm
    have hm' : m ≤ -2 ∨ 2 ≤ m := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      omega
    have h2 : (2 : ℝ) ≤ |(m : ℝ)| := by
      rcases hm' with h | h
      · exact le_abs.mpr (Or.inr (by have : (m : ℝ) ≤ -2 := by exact_mod_cast h
                                     linarith))
      · exact le_abs.mpr (Or.inl (by exact_mod_cast h))
    rw [hK, hRzero, Complex.ofReal_zero, zero_mul]
    rw [abs_mul, abs_of_pos hL]
    nlinarith
  have l1 : ((-1 : ℤ) : ℝ) * L = -L := by push_cast; ring
  have l0 : ((0 : ℤ) : ℝ) * L = 0 := by simp
  have l2 : ((1 : ℤ) : ℝ) * L = L := by simp
  have hsum3 : ∀ φ : ℤ → ℂ, ∑' m : ℤ, EF.weilTest f f (m * L) * φ m =
      ((-B : ℝ) : ℂ) * φ (-1) + ((2 * B : ℝ) : ℂ) * φ 0 + ((-B : ℝ) : ℂ) * φ 1 := by
    intro φ
    rw [tsum_eq_sum (hvan φ), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, l1, l0, l2, hKm, hK0, hKp]
    ring
  have hW := W_offLineLatticeConfig hL hδ hδ' (A := L + 2 * ε) hfc hfc.continuous
    (by rw [show (L + 2 * ε) / 2 = L / 2 + ε by ring]; exact hfs)
    (by rw [show (L + 2 * ε) / 2 = L / 2 + ε by ring]; exact hfs)
  rw [hsum3 (fun m : ℤ => (Real.exp (δ * (m * L)) : ℂ)),
    hsum3 (fun m : ℤ => (Real.exp (-δ * (m * L)) : ℂ))] at hW
  simp only [l1, l0, l2, mul_zero, Real.exp_zero] at hW
  have hW' : (offLineLatticeConfig hL hδ hδ').W f f =
      ((L * (2 * B * (2 - (Real.exp (δ * L) + Real.exp (-(δ * L)))))) : ℝ) := by
    rw [hW, show δ * -L = -(δ * L) by ring, show -δ * -L = δ * L by ring,
      show -δ * L = -(δ * L) by ring]
    push_cast
    ring
  rw [hW', Complex.ofReal_re]
  have hc : 1 < Real.cosh (δ * L) := Real.one_lt_cosh.mpr (mul_pos hδ hL).ne'
  rw [Real.cosh_eq] at hc
  have : 0 < L * (2 * B) := by positivity
  nlinarith

/-- **Nyquist law for the depth of a vertical zero lattice.**  The off-line lattice pair
`{½ ± δ + 2πik/L}` (any depth `δ ∈ (0, ½]`) passes the Weil positivity test on smooth test
functions supported in `[-a, a]` if and only if `a ≤ L/2`, i.e. iff the level is at most
`π` divided by the ordinate spacing. -/
theorem offLineLattice_weil_positive_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re) ↔ a ≤ L / 2 := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨f, hf, hfs, hneg⟩ := exists_re_W_offLineLatticeConfig_neg hL hδ hδ' (lt_of_not_ge hlt)
    exact absurd (h f hf hfs) (not_le.mpr hneg)
  · intro ha f hf hfs
    have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) := hfs.trans (Icc_subset_Icc (by linarith) ha)
    rw [W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf hf.continuous hfs' hfs']
    have := re_integral_mul_conj_self_nonneg f
    have h2 : (2 * (L : ℂ) * ∫ t, f t * conj (f t)).re = 2 * L * (∫ t, f t * conj (f t)).re := by
      rw [show (2 * (L : ℂ)) = ((2 * L : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [h2]
    positivity

end RHTower
