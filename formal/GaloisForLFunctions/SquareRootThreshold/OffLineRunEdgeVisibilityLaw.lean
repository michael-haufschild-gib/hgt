import GaloisForLFunctions.SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw

/-!
# Visibility of an off-line run: the edge law

The background is the doubled on-line lattice `{½ + 2πik/L}`. A **run** replaces the double
on-line points at `N` consecutive ordinates `2πk/L` by reflected off-line pairs `½ ± δ + 2πik/L`.
The local density is unchanged; only the depth profile jumps from `0` to `δ` and back.

For a test `f` supported in `[-a, a]`, `a ≤ L/2`, with Weil kernel `k = f ⋆ f̃`, Poisson summation
on the background gives the exact formula

`W(f, f) = 2L‖f‖² + ∫ k(u) · 2(cosh δu − 1) · Σ_{k in the run} e^{2πiku/L} du`.

The run enters only through the geometric sum `Σ e^{2πiku/L}`, whose modulus is at most
`L/(2|u|)` for `|u| ≤ L/2`, uniformly in the length of the run.

* **Blindness** (`re_W_runConfig_nonneg`): every run, of any length, is invisible at aperture `a`
  when `2δa · sinh(2δa) ≤ 1` and `4a ≤ L`.
* **Edge visibility** (`exists_re_W_runConfig_neg`): when `cosh(δa) > 1 + 8π²`, every sufficiently
  long run is visible at aperture `a` once the background is dense enough. The geometric sum
  splits into one term per edge, `e^{iθ}/(1 − e^{iθ})`, with imaginary part `≈ L/(2πu)`; a test
  straddling the near edge reads it, and the far edge is removed by the Riemann–Lebesgue lemma.

Both thresholds are of order `1/δ` and do not depend on `L` or on the run length. A single pair
(`IsolatedOffLinePairVisibilityLaw`) stays invisible up to aperture `≈ log(4δL)/(2δ)`, and the
infinite off-line lattice (`RHTower.offLineLattice_weil_positive_iff`) up to `L/2`. The visibility
of a dense off-line cluster is carried by the jumps of its depth profile, not by its depth.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The run configuration -/

/-- The run of ordinate indices `k₀, k₀ + 1, …, k₀ + N - 1`. -/
def runSet (k₀ : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.range N).map ⟨fun j : ℕ => k₀ + j, fun i j h => by simpa using h⟩

/-- The doubled on-line lattice `{½ + 2πik/L}` in which every ordinate `2πk/L` with `k ∈ S` carries
the reflected off-line pair `½ ± δ + 2πik/L` instead of the double on-line point. -/
def runConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (S : Finset ℤ) :
    ZeroConfig where
  carrier := ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L δ k) ∪
    Set.range fun k : S => verticalLatticePoint L (-δ) k
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) <;> simp only [verticalLatticePoint] <;>
      constructor <;> linarith
  reflect_mem := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · exact Or.inl (Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩)
    · exact Or.inr ⟨k, (reflect_verticalLatticePoint L δ k).symm⟩
    · exact Or.inl (Or.inr ⟨k, by rw [reflect_verticalLatticePoint, neg_neg]⟩)
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
      (hF.image (verticalLatticePoint L δ))).union (hF.image (verticalLatticePoint L (-δ)))).subset ?_
    rintro _ ⟨((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), h1, h2⟩
    · exact Or.inl (Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩

/-! ### The exact Weil form below the Nyquist aperture -/

/-- Below the Nyquist aperture the run configuration has Weil form `2L‖f‖²` plus, for each `k ∈ S`,
the pair summands minus the removed double on-line summand. -/
theorem W_runConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (S : Finset ℤ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (runConfig hL hδ hδ' S).W f f = 2 * L * (∫ t, f t * conj (f t)) +
      ∑ k ∈ S, (paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * δ) +
        paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * δ) -
        2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) := by
  set Z := runConfig hL hδ hδ' S with hZ
  set K := EF.weilTest f f with hKdef
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hs0 : ∀ k : ℤ, Z.Wsummand f f (verticalLatticePoint L 0 k) =
      2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) := by
    intro k
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_pos (by simp [verticalLatticePoint])]
    simp [hKdef]
  have hsp : ∀ k : ℤ, Z.Wsummand f f (verticalLatticePoint L δ k) =
      paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * δ) := by
    intro k
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_neg (by simp only [verticalLatticePoint]; linarith)]
    simp [hKdef]
  have hsm : ∀ k : ℤ, Z.Wsummand f f (verticalLatticePoint L (-δ) k) =
      paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * δ) := by
    intro k
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_neg (by simp only [verticalLatticePoint]; linarith)]
    push_cast
    rw [show ((k : ℂ) * (2 * π / L)) - I * -(δ : ℂ) = (k : ℂ) * (2 * π / L) + I * δ by ring]
    simp [hKdef]
  -- the full doubled lattice
  have hfull : HasSum (fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ))
      (2 * L * ∫ t, f t * conj (f t)) := by
    have h0 := tsum_weilTest_lattice_eq hL hf hf.continuous hfs hfs
      (fun m : ℤ => (Real.exp (0 * (m * L)) : ℂ)) (by simp)
    have h2 := (hasSum_paperFT_lattice_sub_I_mul hL hK hKs 0).mul_left 2
    rw [h0] at h2
    have hfun : (fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) =
        fun i : ℤ => 2 * paperFT (EF.weilTest f f) ((((i : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ)) := by
      funext k
      simp [hKdef]
    rw [hfun, show (2 * (L : ℂ) * ∫ t, f t * conj (f t)) = 2 * (L * ∫ t, f t * conj (f t)) by ring]
    exact h2
  -- the on-line points off the run
  have hA : HasSum (fun ρ : Set.range (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =>
      Z.Wsummand f f ρ) (2 * L * (∫ t, f t * conj (f t)) -
        ∑ k ∈ S, 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) := by
    have hinj : Function.Injective (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_injective hL 0 h)
    rw [hinj.hasSum_range_iff]
    have := (Finset.hasSum_compl_iff
      (f := fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) S).mpr
      (by rwa [sub_add_cancel])
    have hfun : (Z.Wsummand f f ∘ fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =
        fun x : {k : ℤ // k ∉ S} => 2 * paperFT K ((((x : ℤ) : ℝ) * (2 * π / L) : ℝ) : ℂ) :=
      funext fun k => hs0 k
    rw [hfun]
    exact this
  -- the off-line points of the run
  have hB : ∀ ε : ℝ, HasSum (fun ρ : Set.range (fun k : S => verticalLatticePoint L ε k) =>
      Z.Wsummand f f ρ) (∑ k ∈ S, Z.Wsummand f f (verticalLatticePoint L ε k)) := by
    intro ε
    have hinj : Function.Injective (fun k : S => verticalLatticePoint L ε k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_injective hL ε h)
    rw [hinj.hasSum_range_iff]
    exact Finset.hasSum S (fun k => Z.Wsummand f f (verticalLatticePoint L ε k))
  have hd₁ : Disjoint (Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k)
      (Set.range fun k : S => verticalLatticePoint L δ k) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith
  have hd₂ : Disjoint ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L δ k)
      (Set.range fun k : S => verticalLatticePoint L (-δ) k) := by
    rw [Set.disjoint_left]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) ⟨k', hk'⟩ <;>
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ hA (hB δ)) (hB (-δ))
  have heq := hall.tsum_eq
  rw [ZeroConfig.W]
  refine heq.trans ?_
  simp only [hsp, hsm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- A continuous compactly supported function times a continuous function is integrable. -/
theorem integrable_mul_of_hasCompactSupport {K φ : ℝ → ℂ} (hK : Continuous K)
    (hKc : HasCompactSupport K) (hφ : Continuous φ) : Integrable fun u => K u * φ u :=
  (hK.mul hφ).integrable_of_hasCompactSupport hKc.mul_right

/-- Replacing the double on-line point at ordinate `γ` by the pair of depth `δ` adds
`∫ k(u) · 2(cosh δu − 1) · e^{iγu} du` to the Weil form. -/
theorem paperFT_pair_sub_double {K : ℝ → ℂ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (γ δ : ℝ) :
    paperFT K ((γ : ℂ) - I * δ) + paperFT K ((γ : ℂ) + I * δ) - 2 * paperFT K γ =
      ∫ u, K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) * cexp (I * γ * u) := by
  rw [paperFT_sub_I_mul, paperFT_add_I_mul, paperFT_def, paperFT_def, paperFT_def]
  have hc : ∀ c : ℝ, Continuous fun u : ℝ => ((Real.exp (c * u) : ℝ) : ℂ) * cexp (I * γ * u) :=
    fun c => by fun_prop
  have h1 := integrable_mul_of_hasCompactSupport hK hKc (hc δ)
  have h2 := integrable_mul_of_hasCompactSupport hK hKc (hc (-δ))
  have h3 := integrable_mul_of_hasCompactSupport hK hKc
    (show Continuous fun u : ℝ => cexp (I * γ * u) by fun_prop)
  rw [← EF.cintegral_const_mul, ← integral_add, ← integral_sub]
  · congr 1 with u
    rw [Real.cosh_eq]
    push_cast
    ring_nf
  · exact (h1.congr (Eventually.of_forall fun u => by simp only; ring)).add
      (h2.congr (Eventually.of_forall fun u => by simp only; ring))
  · exact h3.const_mul 2
  · exact h1.congr (Eventually.of_forall fun u => by simp only; ring)
  · exact h2.congr (Eventually.of_forall fun u => by simp only; ring)

/-- **The run formula.** Below the Nyquist aperture,
`W(f, f) = 2L‖f‖² + ∫ k(u) · 2(cosh δu − 1) · Σ_{k ∈ S} e^{2πiku/L} du`. -/
theorem W_runConfig_eq_integral {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (S : Finset ℤ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (runConfig hL hδ hδ' S).W f f = 2 * L * (∫ t, f t * conj (f t)) +
      ∫ u, EF.weilTest f f u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) *
        ∑ k ∈ S, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hKc : HasCompactSupport (EF.weilTest f f) :=
    hasCompactSupport_of_tsupport_subset_Icc (EF.tsupport_weilTest_subset hfs hfs)
  rw [W_runConfig hL hδ hδ' S hf hfs]
  congr 1
  simp_rw [paperFT_pair_sub_double hK hKc, Finset.mul_sum]
  rw [integral_finsetSum]
  intro k _
  exact ((hK.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
    hKc.mul_right.mul_right


/-! ### Blindness: every run is invisible at aperture `O(1/δ)` -/

/-- Jordan's inequality on the circle: `|e^{iθ} − 1| ≥ 2|θ|/π` for `|θ| ≤ π`. -/
theorem two_div_pi_mul_abs_le_norm_cexp_sub_one {θ : ℝ} (hθ : |θ| ≤ π) :
    2 / π * |θ| ≤ ‖cexp (I * θ) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have h1 : 0 ≤ |θ| / 2 := by positivity
  have h2 : |θ| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin h1 h2
  have habs : Real.sin (|θ| / 2) = |Real.sin (θ / 2)| := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [abs_of_nonneg h] at hθ; linarith))]
    · have hn : 0 ≤ Real.sin (-(θ / 2)) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [abs_of_neg h] at hθ; linarith)
      rw [Real.sin_neg] at hn
      rw [abs_of_neg h, abs_of_nonpos (by linarith), neg_div, Real.sin_neg]
  rw [← habs]
  nlinarith [Real.pi_pos]

/-- The geometric sum over a run: `|Σ_{k in the run} e^{2πiku/L}| ≤ L/(2|u|)` for
`0 < |u| ≤ L/2`, whatever the length and position of the run. -/
theorem norm_sum_runSet_le {L u : ℝ} (hL : 0 < L) (hu : u ≠ 0) (huL : |u| ≤ L / 2) (k₀ : ℤ)
    (N : ℕ) :
    ‖∑ k ∈ runSet k₀ N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)‖ ≤ L / (2 * |u|) := by
  set θ : ℝ := 2 * π / L * u with hθ
  set z : ℂ := cexp (I * θ) with hz
  have hθabs : |θ| = 2 * π / L * |u| := by
    rw [hθ, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]
  have hθπ : |θ| ≤ π := by
    rw [hθabs]
    calc 2 * π / L * |u| ≤ 2 * π / L * (L / 2) := by gcongr
      _ = π := by field_simp
  have hu' : 0 < |u| := abs_pos.mpr hu
  have hzlow := two_div_pi_mul_abs_le_norm_cexp_sub_one hθπ
  have hlow : 4 * |u| / L ≤ ‖z - 1‖ := by
    have : 2 / π * |θ| = 4 * |u| / L := by rw [hθabs]; field_simp; ring
    rw [← this]; exact hzlow
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hlow
    have : 0 < 4 * |u| / L := by positivity
    linarith
  have hterm : ∀ j : ℕ, cexp (I * ((((k₀ + j : ℤ) : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      cexp (I * ((k₀ : ℝ) * θ : ℝ)) * z ^ j := by
    intro j
    rw [hz, ← Complex.exp_nat_mul, ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hsum : ∑ k ∈ runSet k₀ N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      cexp (I * ((k₀ : ℝ) * θ : ℝ)) * ((z ^ N - 1) / (z - 1)) := by
    rw [runSet, Finset.sum_map, ← geom_sum_eq hz1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hterm j
  rw [hsum, norm_mul, mul_comm (I : ℂ), Complex.norm_exp_ofReal_mul_I, one_mul, norm_div]
  have hzN : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hz, mul_comm, Complex.norm_exp_ofReal_mul_I, one_pow, norm_one]
        norm_num
  have hpos : 0 < ‖z - 1‖ := lt_of_lt_of_le (by positivity) hlow
  rw [div_le_div_iff₀ hpos (by positivity)]
  calc ‖z ^ N - 1‖ * (2 * |u|) ≤ 2 * (2 * |u|) := by gcongr
    _ = L * (4 * |u| / L) := by field_simp; ring
    _ ≤ L * ‖z - 1‖ := by gcongr

/-- `cosh y − 1 ≤ y sinh y` for `y ≥ 0` (mean value theorem). -/
theorem cosh_sub_one_le_mul_sinh {y : ℝ} (hy : 0 ≤ y) : Real.cosh y - 1 ≤ y * Real.sinh y := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.cosh Real.sinh h
    Real.continuous_cosh.continuousOn fun x _ => Real.hasDerivAt_cosh x
  rw [Real.cosh_zero, sub_zero] at hcd
  have hle : Real.sinh c ≤ Real.sinh y := Real.sinh_le_sinh.mpr hc.2.le
  rw [hcd, div_le_iff₀ h] at hle
  linarith

/-- Pointwise bound for the run integrand on `|u| ≤ 2a ≤ L/2`. -/
theorem norm_run_integrand_le {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 ≤ a)
    (haL : 4 * a ≤ L) (k₀ : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {u : ℝ} (hu : |u| ≤ 2 * a) :
    ‖EF.weilTest f f u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) *
        ∑ k ∈ runSet k₀ N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)‖ ≤
      (∫ t, ‖f t‖ ^ 2) * (L * δ * Real.sinh (2 * δ * a)) := by
  have hE0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hsh : 0 ≤ Real.sinh (2 * δ * a) := Real.sinh_nonneg_iff.mpr (by positivity)
  rcases eq_or_ne u 0 with h0 | h0
  · subst h0
    simp only [mul_zero, Real.cosh_zero, sub_self, Complex.ofReal_zero, zero_mul, mul_zero,
      norm_zero]
    positivity
  have hu' : 0 < |u| := abs_pos.mpr h0
  have hcosh : 0 ≤ Real.cosh (δ * u) - 1 := by linarith [Real.one_le_cosh (δ * u)]
  have hK := norm_weilTest_self_le hf hfc u
  have hS := norm_sum_runSet_le hL h0 (by linarith) k₀ N
  have hmvt : Real.cosh (δ * u) - 1 ≤ δ * |u| * Real.sinh (2 * δ * a) := by
    have h1 := cosh_sub_one_le_mul_sinh (by positivity : 0 ≤ δ * |u|)
    have hc : Real.cosh (δ * u) = Real.cosh (δ * |u|) := by
      rw [← Real.cosh_abs (δ * u), abs_mul, abs_of_pos hδ]
    rw [hc]
    calc Real.cosh (δ * |u|) - 1 ≤ δ * |u| * Real.sinh (δ * |u|) := h1
      _ ≤ δ * |u| * Real.sinh (2 * δ * a) := by
        gcongr
        exact Real.sinh_le_sinh.mpr (by nlinarith)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖EF.weilTest f f u‖ * (2 * (Real.cosh (δ * u) - 1)) *
        ‖∑ k ∈ runSet k₀ N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)‖
      ≤ (∫ t, ‖f t‖ ^ 2) * (2 * (Real.cosh (δ * u) - 1)) * (L / (2 * |u|)) := by gcongr
    _ ≤ (∫ t, ‖f t‖ ^ 2) * (2 * (δ * |u| * Real.sinh (2 * δ * a))) * (L / (2 * |u|)) := by
        gcongr
    _ = (∫ t, ‖f t‖ ^ 2) * (L * δ * Real.sinh (2 * δ * a)) := by field_simp

/-- **Blindness of runs.** For `4a ≤ L`, every run of any length `N` and any position satisfies
`Re W(f, f) ≥ 2L(1 − 2δa sinh(2δa)) ‖f‖²` on tests supported in `[-a, a]`. -/
theorem re_W_runConfig_ge {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ha : 0 ≤ a)
    (haL : 4 * a ≤ L) (k₀ : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * L * (1 - 2 * δ * a * Real.sinh (2 * δ * a)) * ∫ t, ‖f t‖ ^ 2 ≤
      ((runConfig hL hδ hδ' (runSet k₀ N)).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) := hfs.trans (Icc_subset_Icc (by linarith)
    (by linarith))
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hKs : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset (L := 2 * a) (by rwa [show 2 * a / 2 = a by ring])
      (by rwa [show 2 * a / 2 = a by ring])
  rw [W_runConfig_eq_integral hL hδ hδ' _ hf hfs', integral_mul_conj_self_eq, Complex.add_re]
  set F : ℝ → ℂ := fun u => EF.weilTest f f u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) *
    ∑ k ∈ runSet k₀ N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) with hF
  have hFz : ∀ u, u ∉ Icc (-(2 * a)) (2 * a) → F u = 0 := by
    intro u hu
    rw [hF]
    simp only
    rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hKs h)), zero_mul, zero_mul]
  have hbound : ‖∫ u, F u‖ ≤ (∫ t, ‖f t‖ ^ 2) * (L * δ * Real.sinh (2 * δ * a)) * (4 * a) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFz]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(2 * a)) (2 * a))
      (f := F) (C := (∫ t, ‖f t‖ ^ 2) * (L * δ * Real.sinh (2 * δ * a)))
      (by simp) (fun u hu => norm_run_integrand_le hL hδ ha haL k₀ N hf.continuous hfc
        (abs_le.mpr ⟨hu.1, hu.2⟩))
    rwa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      show 2 * a - -(2 * a) = 4 * a by ring] at this
  have hre : -‖∫ u, F u‖ ≤ (∫ u, F u).re := by
    have := Complex.abs_re_le_norm (∫ u, F u)
    linarith [neg_abs_le (∫ u, F u).re]
  rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 by
    rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) = ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]]
  nlinarith

/-- **Every run is invisible below aperture `≈ 0.46/δ`**: if `2δa sinh(2δa) ≤ 1` and `4a ≤ L`, the
run configuration is Weil-nonnegative on all tests supported in `[-a, a]`, whatever the length
and position of the run. -/
theorem re_W_runConfig_nonneg {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 ≤ a) (haL : 4 * a ≤ L) (hδa : 2 * δ * a * Real.sinh (2 * δ * a) ≤ 1) (k₀ : ℤ) (N : ℕ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((runConfig hL hδ hδ' (runSet k₀ N)).W f f).re := by
  refine le_trans ?_ (re_W_runConfig_ge hL hδ hδ' ha haL k₀ N hf hfs)
  have : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun t => by positivity
  have : 0 ≤ 1 - 2 * δ * a * Real.sinh (2 * δ * a) := by linarith
  positivity


/-! ### The edge kernel `e^{iθ}/(1 − e^{iθ})` -/

/-- The edge kernel `w(θ) = e^{iθ}/(1 − e^{iθ}) = −½ + (i/2) cot(θ/2)`: one run edge as seen at
lag `u` through `θ = 2πu/L`. -/
def edgeKernel (θ : ℝ) : ℂ := cexp (I * θ) / (1 - cexp (I * θ))

theorem edgeKernel_im (θ : ℝ) :
    (edgeKernel θ).im = Real.sin θ / (2 - 2 * Real.cos θ) := by
  have hre : (cexp (I * θ)).re = Real.cos θ := by rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have him : (cexp (I * θ)).im = Real.sin θ := by rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  have hn : Complex.normSq (1 - cexp (I * θ)) = 2 - 2 * Real.cos θ := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      hre, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [edgeKernel, Complex.div_im, hn, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, hre, him]
  rcases eq_or_ne (2 - 2 * Real.cos θ) 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

theorem abs_edgeKernel_re_le (θ : ℝ) : |(edgeKernel θ).re| ≤ 1 / 2 := by
  have hre : (cexp (I * θ)).re = Real.cos θ := by rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have him : (cexp (I * θ)).im = Real.sin θ := by rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  have hn : Complex.normSq (1 - cexp (I * θ)) = 2 - 2 * Real.cos θ := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      hre, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [edgeKernel, Complex.div_re, hn, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, hre, him]
  rcases eq_or_ne (2 - 2 * Real.cos θ) 0 with h | h
  · rw [h]; simp
  · have hnum : Real.cos θ * (1 - Real.cos θ) + Real.sin θ * (0 - Real.sin θ) =
        -(1 / 2) * (2 - 2 * Real.cos θ) := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [← add_div, hnum, mul_div_assoc, div_self h, mul_one, abs_neg,
      abs_of_pos (by norm_num)]

/-- For `0 < θ ≤ π/2` the edge kernel has imaginary part at least `2/(πθ)`. -/
theorem two_div_pi_mul_le_edgeKernel_im {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2) :
    2 / (π * θ) ≤ (edgeKernel θ).im := by
  rw [edgeKernel_im]
  have hs := Real.mul_le_sin h0.le h1
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hc1 : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) h0
    rwa [Real.cos_zero] at this
  have hd : 0 < 2 - 2 * Real.cos θ := by linarith
  rw [div_le_div_iff₀ (by positivity) hd]
  have hπ := Real.pi_pos
  have h3 : 2 / π * θ * (π * θ) = 2 * θ ^ 2 := by field_simp
  have h4 : 2 / π * θ * (π * θ) ≤ Real.sin θ * (π * θ) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  linarith

/-- For `-π/2 ≤ θ < 0` the edge kernel has imaginary part at most `2/(πθ)`. -/
theorem edgeKernel_im_le_two_div_pi_mul {θ : ℝ} (h0 : θ < 0) (h1 : -(π / 2) ≤ θ) :
    (edgeKernel θ).im ≤ 2 / (π * θ) := by
  have h := two_div_pi_mul_le_edgeKernel_im (θ := -θ) (by linarith) (by linarith)
  rw [edgeKernel_im, Real.sin_neg, Real.cos_neg] at h
  rw [edgeKernel_im]
  have : 2 / (π * -θ) = -(2 / (π * θ)) := by rw [mul_neg, div_neg]
  rw [this, neg_div] at h
  linarith

/-- The run `1, …, N` sums to the edge kernel times `1 − e^{iNθ}`. -/
theorem sum_runSet_one_eq {L u : ℝ} (hz : cexp (I * ((2 * π / L * u : ℝ) : ℂ)) ≠ 1) (N : ℕ) :
    ∑ k ∈ runSet 1 N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      edgeKernel (2 * π / L * u) * (1 - cexp (I * ((2 * π / L * u : ℝ) : ℂ)) ^ N) := by
  set z := cexp (I * ((2 * π / L * u : ℝ) : ℂ)) with hzdef
  have hterm : ∀ j : ℕ, cexp (I * ((((1 + j : ℤ) : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      z * z ^ j := by
    intro j
    rw [hzdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [runSet, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, geom_sum_eq hz, edgeKernel,
    ← hzdef]
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring


/-! ### The edge test -/

/-- Correlation of two localized functions: `u ↦ ∫ α(t) β(t − u) dt` lives on
`|u − (p − q)| < 2r`, is integrable, and has total mass `(∫ α)(∫ β)`. -/
theorem correlation_support_integrable_integral {α β : ℝ → ℝ} (hα : Continuous α)
    (hβ : Continuous β) {p q r : ℝ} (hαs : ∀ t, α t ≠ 0 → |t - p| < r)
    (hβs : ∀ t, β t ≠ 0 → |t - q| < r) :
    (∀ u, (∫ t, α t * β (t - u)) ≠ 0 → |u - (p - q)| < 2 * r) ∧
      Integrable (fun u => ∫ t, α t * β (t - u)) ∧
      ∫ u, (∫ t, α t * β (t - u)) = (∫ t, α t) * ∫ t, β t := by
  have hloc : ∀ u t, α t * β (t - u) ≠ 0 → |t - p| < r ∧ |u - (p - q)| < 2 * r := by
    intro u t h
    have h1 := hαs t (left_ne_zero_of_mul h)
    have h2 := hβs (t - u) (right_ne_zero_of_mul h)
    refine ⟨h1, ?_⟩
    calc |u - (p - q)| = |(t - p) + -(t - u - q)| := by congr 1; ring
      _ ≤ |t - p| + |-(t - u - q)| := abs_add_le _ _
      _ < r + r := by rw [abs_neg]; exact add_lt_add h1 h2
      _ = 2 * r := by ring
  set F : ℝ × ℝ → ℝ := fun x => α x.2 * β (x.2 - x.1) with hF
  have hFc : Continuous F := (hα.comp continuous_snd).mul
    (hβ.comp (continuous_snd.sub continuous_fst))
  have hFs : HasCompactSupport F := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := p - q - 2 * r) (b := p - q + 2 * r)).prod
        (isCompact_Icc (a := p - r) (b := p + r))) fun x hx => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := hloc x.1 x.2 hne
    exact hx ⟨⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩,
      ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩⟩
  have hFi : Integrable F (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  refine ⟨fun u hu => ?_, hFi.integral_prod_left, ?_⟩
  · by_contra hge
    apply hu
    have : (fun t => α t * β (t - u)) = fun _ => 0 := by
      funext t
      by_contra hne
      exact hge (hloc u t hne).2
    rw [this, integral_zero]
  · have hswap := integral_integral_swap (μ := volume) (ν := volume)
      (f := fun u t => α t * β (t - u)) hFi
    rw [hswap]
    have hin : ∀ t, ∫ u, α t * β (t - u) = α t * ∫ t, β t := by
      intro t
      rw [integral_const_mul, integral_sub_left_eq_self (fun x => β x) volume t]
    simp_rw [hin]
    rw [integral_mul_const]

/-- **The edge test.** A smooth test supported in `[-a, a]`: a left bump plus `i` times a right
bump. The imaginary part of its Weil kernel is `c₊ − c₋` with `c₊, c₋ ≥ 0` supported in `(a, 2a)`
and `(-2a, -a)`, each of mass `P²`, while `‖g‖² = 2B ≤ 2P` and `P ≥ a/4`. -/
theorem exists_edgeTest {a : ℝ} (ha : 0 < a) :
    ∃ g : ℝ → ℂ, ∃ P B : ℝ, ∃ cp cm : ℝ → ℝ,
      ContDiff ℝ 2 g ∧ tsupport g ⊆ Icc (-a) a ∧ ∫ t, ‖g t‖ ^ 2 = 2 * B ∧ 0 ≤ B ∧
      B ≤ P ∧ a / 4 ≤ P ∧
      (∀ u, (EF.weilTest g g u).im = cp u - cm u) ∧ (∀ u, 0 ≤ cp u) ∧ (∀ u, 0 ≤ cm u) ∧
      (∀ u, cp u ≠ 0 → a < u ∧ u < 2 * a) ∧ (∀ u, cm u ≠ 0 → -(2 * a) < u ∧ u < -a) ∧
      Integrable cp ∧ Integrable cm ∧ ∫ u, cp u = P ^ 2 ∧ ∫ u, cm u = P ^ 2 := by
  obtain ⟨b, hbIn, hbOut⟩ : ∃ b : ContDiffBump (0 : ℝ), b.rIn = a / 8 ∧ b.rOut = a / 4 :=
    ⟨⟨a / 8, a / 4, by positivity, by linarith⟩, rfl, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = ⇑b := ⟨_, rfl⟩
  have hφc : ContDiff ℝ 2 φ := hφ ▸ b.contDiff
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => hφ ▸ b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => hφ ▸ b.le_one
  have hφone : ∀ x, |x| ≤ a / 8 → φ x = 1 := by
    intro x hx
    rw [hφ]
    exact b.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hbIn]; exact hx)
  have hφs : ∀ x, φ x ≠ 0 → |x - 0| < a / 4 := by
    intro x hx
    have : x ∈ Function.support b := by rw [← hφ]; exact hx
    rw [b.support_eq, hbOut, Metric.mem_ball, Real.dist_eq] at this
    exact this
  have hφcs : HasCompactSupport φ := hφ ▸ b.hasCompactSupport
  have hφi : Integrable φ := hφc.continuous.integrable_of_hasCompactSupport hφcs
  have hsqc : HasCompactSupport fun x => φ x ^ 2 := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(a / 4)) (b := a / 4)) fun x hx => ?_
    by_contra hne
    have h := abs_lt.mp (hφs x fun h0 => hne (by rw [h0]; ring))
    exact hx ⟨by linarith, by linarith⟩
  have hsq : Integrable fun x => φ x ^ 2 :=
    (hφc.continuous.pow 2).integrable_of_hasCompactSupport hsqc
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℝ → ℝ, φ₁ = fun t => φ (t + 3 * a / 4) := ⟨_, rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : ℝ → ℝ, φ₂ = fun t => φ (t - 3 * a / 4) := ⟨_, rfl⟩
  have h₁c : Continuous φ₁ := hφ₁ ▸ hφc.continuous.comp (continuous_id.add continuous_const)
  have h₂c : Continuous φ₂ := hφ₂ ▸ hφc.continuous.comp (continuous_id.sub continuous_const)
  have h₁0 : ∀ t, 0 ≤ φ₁ t := fun t => by rw [hφ₁]; exact hφ0 _
  have h₂0 : ∀ t, 0 ≤ φ₂ t := fun t => by rw [hφ₂]; exact hφ0 _
  have h₁s : ∀ t, φ₁ t ≠ 0 → |t - -(3 * a / 4)| < a / 4 := by
    intro t ht
    rw [hφ₁] at ht
    have := hφs _ ht
    rwa [sub_zero, show t + 3 * a / 4 = t - -(3 * a / 4) by ring] at this
  have h₂s : ∀ t, φ₂ t ≠ 0 → |t - 3 * a / 4| < a / 4 := by
    intro t ht
    rw [hφ₂] at ht
    have := hφs _ ht
    rwa [sub_zero] at this
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun t => (φ₁ t : ℂ) + I * (φ₂ t : ℂ) := ⟨_, rfl⟩
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgsupp : ∀ t, g t ≠ 0 → -a < t ∧ t < a := by
    intro t ht
    by_cases h1 : φ₁ t = 0
    · have h2 : φ₂ t ≠ 0 := by intro h2; apply ht; simp [hg, h1, h2]
      have := abs_lt.mp (h₂s t h2)
      exact ⟨by linarith, by linarith⟩
    · have := abs_lt.mp (h₁s t h1)
      exact ⟨by linarith, by linarith⟩
  set P : ℝ := ∫ x, φ x with hP
  set B : ℝ := ∫ x, φ x ^ 2 with hB
  have hP₁ : ∫ t, φ₁ t = P := by rw [hφ₁]; exact integral_add_right_eq_self (fun x => φ x) _
  have hP₂ : ∫ t, φ₂ t = P := by rw [hφ₂]; exact integral_sub_right_eq_self (fun x => φ x) _
  -- the two correlations
  obtain ⟨hps, hpi, hpm⟩ := correlation_support_integrable_integral h₂c h₁c h₂s h₁s
  obtain ⟨hms, hmi, hmm⟩ := correlation_support_integrable_integral h₁c h₂c h₁s h₂s
  refine ⟨g, P, B, fun u => ∫ t, φ₂ t * φ₁ (t - u), fun u => ∫ t, φ₁ t * φ₂ (t - u),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpi, hmi, ?_, ?_⟩
  · rw [hg, hφ₁, hφ₂]
    exact (Complex.ofRealCLM.contDiff.comp (hφc.comp (contDiff_id.add contDiff_const))).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (hφc.comp (contDiff_id.sub contDiff_const))))
  · refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have := hgsupp t ht
    exact ⟨this.1.le, this.2.le⟩
  · have hpt : ∀ t, ‖g t‖ ^ 2 = φ (t + 3 * a / 4) ^ 2 + φ (t - 3 * a / 4) ^ 2 := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, hg, hφ₁, hφ₂]
      simp only
      rw [mul_comm I, Complex.normSq_add_mul_I]
    simp_rw [hpt]
    rw [integral_add (hsq.comp_add_right _) (hsq.comp_sub_right _),
      integral_add_right_eq_self (fun x => φ x ^ 2), integral_sub_right_eq_self
        (fun x => φ x ^ 2)]
    ring
  · exact integral_nonneg fun x => sq_nonneg _
  · refine integral_mono hsq hφi fun x => ?_
    have := hφ0 x; have := hφ1 x
    simp only
    nlinarith
  · have h1 : ∫ x in Icc (-(a / 8)) (a / 8), φ x = ∫ x in Icc (-(a / 8)) (a / 8), (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc fun x hx => hφone x (abs_le.mpr hx)
    have h2 : ∫ x in Icc (-(a / 8)) (a / 8), φ x ≤ ∫ x, φ x :=
      setIntegral_le_integral hφi (Eventually.of_forall hφ0)
    rw [h1, setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)] at h2
    linarith
  · intro u
    have hgs : HasCompactSupport g := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun t ht => ?_
      by_contra hne
      have := hgsupp t hne
      exact ht ⟨this.1.le, this.2.le⟩
    have hint : Integrable fun t => g t * conj (g (t - u)) :=
      (hgc.mul (continuous_conj.comp (hgc.comp (continuous_id.sub continuous_const))))
        |>.integrable_of_hasCompactSupport hgs.mul_right
    rw [weilTest_apply, ← RCLike.im_to_complex, ← integral_im hint]
    simp only
    have hpt : ∀ t, RCLike.im (g t * conj (g (t - u))) =
        φ₂ t * φ₁ (t - u) - φ₁ t * φ₂ (t - u) := by
      intro t
      rw [hg]
      simp only [RCLike.im_to_complex, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]
      ring
    simp_rw [hpt]
    have hc₁ : HasCompactSupport φ₁ := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := -(a / 2))) fun t ht => ?_
      by_contra hne
      have := abs_lt.mp (h₁s t hne)
      exact ht ⟨by linarith, by linarith⟩
    have hc₂ : HasCompactSupport φ₂ := by
      refine HasCompactSupport.intro (isCompact_Icc (a := a / 2) (b := a)) fun t ht => ?_
      by_contra hne
      have := abs_lt.mp (h₂s t hne)
      exact ht ⟨by linarith, by linarith⟩
    exact integral_sub
      ((h₂c.mul (h₁c.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
        hc₂.mul_right)
      ((h₁c.mul (h₂c.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
        hc₁.mul_right)
  · exact fun u => integral_nonneg fun t => mul_nonneg (h₂0 _) (h₁0 _)
  · exact fun u => integral_nonneg fun t => mul_nonneg (h₁0 _) (h₂0 _)
  · intro u hu
    have := abs_lt.mp (hps u hu)
    exact ⟨by linarith, by linarith⟩
  · intro u hu
    have := abs_lt.mp (hms u hu)
    exact ⟨by linarith, by linarith⟩
  · rw [hpm, hP₁, hP₂]; ring
  · rw [hmm, hP₁, hP₂]; ring

end GaloisForLFunctions.SquareRootThreshold
