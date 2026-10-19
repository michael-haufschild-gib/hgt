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


/-! ### Edge visibility -/

/-- The edge integrand `k(u) · 2(cosh δu − 1) · w(2πu/L)`. -/
def edgeIntegrand (L δ : ℝ) (K : ℝ → ℂ) (u : ℝ) : ℂ :=
  K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) * edgeKernel (2 * π / L * u)

/-- Riemann–Lebesgue in the normalisation of `paperFT`: `h_G(cN) → 0`. -/
theorem tendsto_paperFT_mul_nat (G : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => paperFT G ((c * N : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hneg : -(c / (2 * π)) < 0 := neg_neg_of_pos (by positivity)
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * -(c / (2 * π))) atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hneg
  have h2 := (Real.zero_at_infty_fourier G).comp (h1.mono_right atBot_le_cocompact)
  refine Tendsto.congr (fun N => ?_) h2
  simp only [Function.comp_apply]
  rw [EF.paperFT_ofReal_eq_fourier]
  field_simp

/-- `cosh(δu) − 1 ≤ δ|u| sinh(2δa)` for `|u| ≤ 2a`. -/
theorem cosh_mul_sub_one_le {δ a u : ℝ} (hδ : 0 < δ) (hu : |u| ≤ 2 * a) :
    Real.cosh (δ * u) - 1 ≤ δ * |u| * Real.sinh (2 * δ * a) := by
  have h1 := cosh_sub_one_le_mul_sinh (by positivity : 0 ≤ δ * |u|)
  have hc : Real.cosh (δ * u) = Real.cosh (δ * |u|) := by
    rw [← Real.cosh_abs (δ * u), abs_mul, abs_of_pos hδ]
  rw [hc]
  calc Real.cosh (δ * |u|) - 1 ≤ δ * |u| * Real.sinh (δ * |u|) := h1
    _ ≤ δ * |u| * Real.sinh (2 * δ * a) := by
      gcongr
      exact Real.sinh_le_sinh.mpr (by nlinarith)

/-- The run factor `k(u) · 2(cosh δu − 1)` vanishes at `u = 0` and for `|u| > 2a`. -/
theorem run_factor_support {δ a : ℝ} {K : ℝ → ℂ} (hK0 : ∀ u, ¬ |u| ≤ 2 * a → K u = 0) {u : ℝ}
    (h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) ≠ 0) : u ≠ 0 ∧ |u| ≤ 2 * a :=
  ⟨fun h0 => h (by simp [h0]), by_contra fun hu => h (by simp [hK0 u hu])⟩

theorem norm_run_factor_le {δ a B : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) {K : ℝ → ℂ}
    (hK0 : ∀ u, ¬ |u| ≤ 2 * a → K u = 0) (hKn : ∀ u, ‖K u‖ ≤ 2 * B) (u : ℝ) :
    ‖K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ ≤
      2 * B * (2 * δ * |u| * Real.sinh (2 * δ * a)) := by
  have hB : 0 ≤ 2 * B := (norm_nonneg _).trans (hKn 0)
  have hs : 0 ≤ Real.sinh (2 * δ * a) := Real.sinh_nonneg_iff.mpr (by positivity)
  by_cases h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) = 0
  · rw [h, norm_zero]; positivity
  obtain ⟨-, hu⟩ := run_factor_support hK0 h
  have hc0 : 0 ≤ Real.cosh (δ * u) - 1 := by linarith [Real.one_le_cosh (δ * u)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := cosh_mul_sub_one_le (a := a) hδ hu
  calc ‖K u‖ * (2 * (Real.cosh (δ * u) - 1)) ≤ 2 * B * (2 * (Real.cosh (δ * u) - 1)) := by
        gcongr; exact hKn u
    _ ≤ 2 * B * (2 * δ * |u| * Real.sinh (2 * δ * a)) :=
        mul_le_mul_of_nonneg_left (by linarith) hB

theorem norm_run_factor_le_cosh {δ a B : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) {K : ℝ → ℂ}
    (hK0 : ∀ u, ¬ |u| ≤ 2 * a → K u = 0) (hKn : ∀ u, ‖K u‖ ≤ 2 * B) (u : ℝ) :
    ‖K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ ≤
      2 * B * (2 * (Real.cosh (2 * δ * a) - 1)) := by
  have hB : 0 ≤ 2 * B := (norm_nonneg _).trans (hKn 0)
  have h2 : 0 ≤ Real.cosh (2 * δ * a) - 1 := by linarith [Real.one_le_cosh (2 * δ * a)]
  by_cases h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) = 0
  · rw [h, norm_zero]; positivity
  obtain ⟨-, hu⟩ := run_factor_support hK0 h
  have hc0 : 0 ≤ Real.cosh (δ * u) - 1 := by linarith [Real.one_le_cosh (δ * u)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcc : Real.cosh (δ * u) ≤ Real.cosh (2 * δ * a) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_pos hδ, abs_of_nonneg (by positivity : 0 ≤ 2 * δ * a)]
    nlinarith
  calc ‖K u‖ * (2 * (Real.cosh (δ * u) - 1)) ≤ 2 * B * (2 * (Real.cosh (δ * u) - 1)) := by
        gcongr; exact hKn u
    _ ≤ 2 * B * (2 * (Real.cosh (2 * δ * a) - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hB

/-- `|e^{2πiu/L} − 1| ≥ 4|u|/L` for `|u| ≤ L/2`. -/
theorem four_mul_abs_div_le_norm_cexp_sub_one {L u : ℝ} (hL : 0 < L) (hu : |u| ≤ L / 2) :
    4 * |u| / L ≤ ‖cexp (I * ((2 * π / L * u : ℝ) : ℂ)) - 1‖ := by
  have hθ : |2 * π / L * u| ≤ π := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]
    calc 2 * π / L * |u| ≤ 2 * π / L * (L / 2) := by gcongr
      _ = π := by field_simp
  have h := two_div_pi_mul_abs_le_norm_cexp_sub_one hθ
  have : 2 / π * |2 * π / L * u| = 4 * |u| / L := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]; field_simp; ring
  rwa [this] at h

/-- `|w(2πu/L)| ≤ L/(4|u|)` for `0 < |u| ≤ L/2`. -/
theorem norm_edgeKernel_le {L u : ℝ} (hL : 0 < L) (hu0 : u ≠ 0) (hu : |u| ≤ L / 2) :
    ‖edgeKernel (2 * π / L * u)‖ ≤ L / (4 * |u|) := by
  have hu' : 0 < |u| := abs_pos.mpr hu0
  have h := four_mul_abs_div_le_norm_cexp_sub_one hL hu
  rw [edgeKernel, norm_div, mul_comm I, Complex.norm_exp_ofReal_mul_I, norm_sub_rev,
    ← mul_comm I]
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h) (by positivity)]
  calc 1 * (4 * |u|) = L * (4 * |u| / L) := by field_simp
    _ ≤ L * ‖cexp (I * ((2 * π / L * u : ℝ) : ℂ)) - 1‖ := by gcongr

/-- The edge integrand is integrable. -/
theorem integrable_edgeIntegrand {L δ a B : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 ≤ a)
    (haL : 4 * a ≤ L) {K : ℝ → ℂ} (hKc : Continuous K) (hK0 : ∀ u, ¬ |u| ≤ 2 * a → K u = 0)
    (hKn : ∀ u, ‖K u‖ ≤ 2 * B) : Integrable (edgeIntegrand L δ K) := by
  have hB : 0 ≤ B := by have := (norm_nonneg _).trans (hKn 0); linarith
  have hs : 0 ≤ Real.sinh (2 * δ * a) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hn : ∀ u, ‖edgeIntegrand L δ K u‖ ≤ B * L * δ * Real.sinh (2 * δ * a) := by
    intro u
    by_cases h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) = 0
    · rw [edgeIntegrand, h, zero_mul, norm_zero]; positivity
    obtain ⟨hu0, hu⟩ := run_factor_support hK0 h
    have hu' : 0 < |u| := abs_pos.mpr hu0
    rw [edgeIntegrand, norm_mul]
    calc ‖K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ * ‖edgeKernel (2 * π / L * u)‖
        ≤ 2 * B * (2 * δ * |u| * Real.sinh (2 * δ * a)) * (L / (4 * |u|)) :=
          mul_le_mul (norm_run_factor_le hδ ha hK0 hKn u)
            (norm_edgeKernel_le hL hu0 (by linarith)) (norm_nonneg _) (by positivity)
      _ = B * L * δ * Real.sinh (2 * δ * a) := by field_simp; ring
  have hm : AEStronglyMeasurable (edgeIntegrand L δ K) := by
    have hw : Measurable fun u : ℝ => edgeKernel (2 * π / L * u) := by
      unfold edgeKernel
      exact (Continuous.measurable (by fun_prop)).div (Continuous.measurable (by fun_prop))
    have hE : Continuous fun u => K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) := by fun_prop
    exact (hE.measurable.mul hw).aestronglyMeasurable
  have hon : IntegrableOn (edgeIntegrand L δ K) (Icc (-(2 * a)) (2 * a)) :=
    Measure.integrableOn_of_bounded (by simp) hm (Eventually.of_forall hn)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro u hu
  have h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) ≠ 0 := fun h0 =>
    hu (by rw [edgeIntegrand, h0, zero_mul])
  exact abs_le.mp (run_factor_support hK0 h).2

/-- **The two edges.** The run integral splits into the edge integral minus its Fourier
transform at `2πN/L`, the far edge. -/
theorem integral_run_eq_edge {L δ a B : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 ≤ a)
    (haL : 4 * a ≤ L)
    {K : ℝ → ℂ} (hKc : Continuous K) (hK0 : ∀ u, ¬ |u| ≤ 2 * a → K u = 0)
    (hKn : ∀ u, ‖K u‖ ≤ 2 * B) (N : ℕ) :
    ∫ u, K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) *
        ∑ k ∈ runSet 1 N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      (∫ u, edgeIntegrand L δ K u) - paperFT (edgeIntegrand L δ K) ((2 * π / L * N : ℝ) : ℂ) := by
  have hGi := integrable_edgeIntegrand hL hδ ha haL hKc hK0 hKn
  have hsplit : ∀ u, K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) *
      ∑ k ∈ runSet 1 N, cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) =
      edgeIntegrand L δ K u - edgeIntegrand L δ K u * cexp (I * ((2 * π / L * N : ℝ) : ℂ) * u) := by
    intro u
    by_cases h : K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) = 0
    · rw [edgeIntegrand, h]; ring
    obtain ⟨hu0, hu⟩ := run_factor_support hK0 h
    have hz1 : cexp (I * ((2 * π / L * u : ℝ) : ℂ)) ≠ 1 := by
      intro h1
      have := four_mul_abs_div_le_norm_cexp_sub_one hL (u := u) (by linarith)
      rw [h1, sub_self, norm_zero] at this
      have : 0 < 4 * |u| / L := by have := abs_pos.mpr hu0; positivity
      linarith
    rw [sum_runSet_one_eq hz1 N, edgeIntegrand]
    have hpow : cexp (I * ((2 * π / L * u : ℝ) : ℂ)) ^ N =
        cexp (I * ((2 * π / L * N : ℝ) : ℂ) * u) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hpow]
    ring
  rw [paperFT_def, ← integral_sub hGi]
  · exact integral_congr_ae (Eventually.of_forall hsplit)
  · refine hGi.mul_of_top_left ?_
    exact memLp_top_of_bound (by fun_prop) 1 (Eventually.of_forall fun u => by
      rw [mul_assoc, ← Complex.ofReal_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I])

/-- Pointwise bound on the real part of the edge integrand: the near edge contributes at most
`-(cosh δa − 1) L/(π²a) · (c₊ + c₋)`, the rest at most half the run factor. -/
theorem re_edgeIntegrand_le {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 < a)
    (haL : 8 * a ≤ L) {K : ℝ → ℂ} {cp cm : ℝ → ℝ} (hIm : ∀ u, (K u).im = cp u - cm u)
    (hcp0 : ∀ u, 0 ≤ cp u) (hcm0 : ∀ u, 0 ≤ cm u) (hcps : ∀ u, cp u ≠ 0 → a < u ∧ u < 2 * a)
    (hcms : ∀ u, cm u ≠ 0 → -(2 * a) < u ∧ u < -a) (u : ℝ) :
    (edgeIntegrand L δ K u).re ≤ ‖K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ / 2 -
      (Real.cosh (δ * a) - 1) * L / (π ^ 2 * a) * (cp u + cm u) := by
  have hπ := Real.pi_pos
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = K u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = edgeKernel (2 * π / L * u) := ⟨_, rfl⟩
  have hG : edgeIntegrand L δ K u = E * w := by rw [hE, hw]; rfl
  rw [hG, ← hE, Complex.mul_re]
  have hEim : E.im = (cp u - cm u) * (2 * (Real.cosh (δ * u) - 1)) := by
    rw [hE, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hIm u]
  have hreb : E.re * w.re ≤ ‖E‖ / 2 := by
    have h1 : |w.re| ≤ 1 / 2 := hw ▸ abs_edgeKernel_re_le (2 * π / L * u)
    have h2 := Complex.abs_re_le_norm E
    calc E.re * w.re ≤ |E.re * w.re| := le_abs_self _
      _ = |E.re| * |w.re| := abs_mul _ _
      _ ≤ ‖E‖ * (1 / 2) := by gcongr
      _ = ‖E‖ / 2 := by ring
  have hc1 : 0 ≤ Real.cosh (δ * a) - 1 := by linarith [Real.one_le_cosh (δ * a)]
  have hLa : 0 < L / (2 * π ^ 2 * a) := by positivity
  have hc₀ : (Real.cosh (δ * a) - 1) * L / (π ^ 2 * a) =
      2 * (Real.cosh (δ * a) - 1) * (L / (2 * π ^ 2 * a)) := by field_simp
  rw [hc₀, hEim]
  by_cases hp : cp u = 0
  · by_cases hn : cm u = 0
    · rw [hp, hn]
      simp only [sub_self, zero_mul, add_zero, mul_zero, sub_zero]
      exact hreb
    obtain ⟨hu1, hu2⟩ := hcms u hn
    have hu0 : 0 < -u := by linarith
    have hθ0 : 2 * π / L * u < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have hθ1 : -(π / 2) ≤ 2 * π / L * u := by
      have : 2 * π / L * (-u) ≤ π / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hL (by norm_num)]; nlinarith
      linarith
    have hwi : L / (2 * π ^ 2 * a) ≤ -w.im := by
      have h := edgeKernel_im_le_two_div_pi_mul hθ0 hθ1
      have he : 2 / (π * (2 * π / L * u)) = -(L / (π ^ 2 * (-u))) := by field_simp
      rw [he, ← hw] at h
      have : L / (2 * π ^ 2 * a) ≤ L / (π ^ 2 * (-u)) :=
        div_le_div_of_nonneg_left hL.le (by positivity) (by nlinarith)
      linarith
    have hcc : Real.cosh (δ * a) ≤ Real.cosh (δ * u) := by
      rw [Real.cosh_le_cosh, abs_of_pos (mul_pos hδ ha), abs_mul, abs_of_pos hδ,
        abs_of_neg (by linarith)]
      nlinarith
    have hkey : 2 * (Real.cosh (δ * a) - 1) * (L / (2 * π ^ 2 * a)) * cm u ≤
        cm u * (2 * (Real.cosh (δ * u) - 1)) * -w.im := by
      calc 2 * (Real.cosh (δ * a) - 1) * (L / (2 * π ^ 2 * a)) * cm u
          = cm u * (2 * (Real.cosh (δ * a) - 1)) * (L / (2 * π ^ 2 * a)) := by ring
        _ ≤ cm u * (2 * (Real.cosh (δ * u) - 1)) * -w.im :=
            mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (hcm0 u)) hwi hLa.le
              (mul_nonneg (hcm0 u) (by linarith))
    rw [hp]
    nlinarith
  obtain ⟨hu1, hu2⟩ := hcps u hp
  have hm : cm u = 0 := by
    by_contra hm; have := (hcms u hm).2; linarith
  have hu0 : 0 < u := by linarith
  have hθ0 : 0 < 2 * π / L * u := mul_pos (by positivity) hu0
  have hθ1 : 2 * π / L * u ≤ π / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hL (by norm_num)]; nlinarith
  have hwi : L / (2 * π ^ 2 * a) ≤ w.im := by
    have h := two_div_pi_mul_le_edgeKernel_im hθ0 hθ1
    have he : 2 / (π * (2 * π / L * u)) = L / (π ^ 2 * u) := by field_simp
    rw [he, ← hw] at h
    exact le_trans (div_le_div_of_nonneg_left hL.le (by positivity) (by nlinarith)) h
  have hcc : Real.cosh (δ * a) ≤ Real.cosh (δ * u) := by
    rw [Real.cosh_le_cosh, abs_of_pos (mul_pos hδ ha), abs_of_pos (mul_pos hδ hu0)]
    nlinarith
  have hkey : 2 * (Real.cosh (δ * a) - 1) * (L / (2 * π ^ 2 * a)) * cp u ≤
      cp u * (2 * (Real.cosh (δ * u) - 1)) * w.im := by
    calc 2 * (Real.cosh (δ * a) - 1) * (L / (2 * π ^ 2 * a)) * cp u
        = cp u * (2 * (Real.cosh (δ * a) - 1)) * (L / (2 * π ^ 2 * a)) := by ring
      _ ≤ cp u * (2 * (Real.cosh (δ * u) - 1)) * w.im :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (hcp0 u)) hwi hLa.le
            (mul_nonneg (hcp0 u) (by linarith))
  rw [hm]
  nlinarith

/-- **The edge estimate.** For a test with the properties of `exists_edgeTest`, `8a ≤ L` and the
run `1, …, N`:
`Re W ≤ 4LB + 8aB(cosh 2δa − 1) − 2(cosh δa − 1)LP²/(π²a) + |h_G(2πN/L)|`.
The negative term is the near edge, read through `Im w(θ) ≥ 2/(πθ)`; the last term is the far
edge. -/
theorem re_W_runConfig_le_edge {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haL : 8 * a ≤ L) {g : ℝ → ℂ} {P B : ℝ} {cp cm : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Icc (-a) a) (hgB : ∫ t, ‖g t‖ ^ 2 = 2 * B)
    (hIm : ∀ u, (EF.weilTest g g u).im = cp u - cm u) (hcp0 : ∀ u, 0 ≤ cp u)
    (hcm0 : ∀ u, 0 ≤ cm u) (hcps : ∀ u, cp u ≠ 0 → a < u ∧ u < 2 * a)
    (hcms : ∀ u, cm u ≠ 0 → -(2 * a) < u ∧ u < -a) (hcpi : Integrable cp)
    (hcmi : Integrable cm) (hcpm : ∫ u, cp u = P ^ 2) (hcmm : ∫ u, cm u = P ^ 2) (N : ℕ) :
    ((runConfig hL hδ hδ' (runSet 1 N)).W g g).re ≤
      4 * L * B + 8 * a * B * (Real.cosh (2 * δ * a) - 1) -
        2 * (Real.cosh (δ * a) - 1) * L * P ^ 2 / (π ^ 2 * a) +
        ‖paperFT (edgeIntegrand L δ (EF.weilTest g g)) ((2 * π / L * N : ℝ) : ℂ)‖ := by
  have hgs' : tsupport g ⊆ Icc (-(L / 2)) (L / 2) :=
    hgs.trans (Icc_subset_Icc (by linarith) (by linarith))
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hKc : Continuous (EF.weilTest g g) :=
    (EF.weilTest_contDiff hg hg.continuous hgc).continuous
  have hKs : tsupport (EF.weilTest g g) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset (L := 2 * a) (by rwa [show 2 * a / 2 = a by ring])
      (by rwa [show 2 * a / 2 = a by ring])
  have hK0 : ∀ u, ¬ |u| ≤ 2 * a → EF.weilTest g g u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport (fun h => hu (abs_le.mpr (hKs h)))
  have hKn : ∀ u, ‖EF.weilTest g g u‖ ≤ 2 * B := fun u =>
    hgB ▸ norm_weilTest_self_le hg.continuous hgc u
  have hGi := integrable_edgeIntegrand hL hδ ha.le (by linarith) hKc hK0 hKn
  rw [W_runConfig_eq_integral hL hδ hδ' _ hg hgs',
    integral_run_eq_edge hL hδ ha.le (by linarith) hKc hK0 hKn N, integral_mul_conj_self_eq, hgB]
  have hreG : (∫ u, edgeIntegrand L δ (EF.weilTest g g) u).re =
      ∫ u, (edgeIntegrand L δ (EF.weilTest g g) u).re := (integral_re hGi).symm
  rw [Complex.add_re, Complex.sub_re, hreG]
  have hEc : Continuous fun u => EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) := by
    fun_prop
  have hEs : HasCompactSupport fun u => EF.weilTest g g u *
      ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun u hu => ?_
    by_contra h
    exact hu (abs_le.mp (run_factor_support hK0 h).2)
  have hEi : Integrable fun u => ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ :=
    (hEc.integrable_of_hasCompactSupport (μ := volume) hEs).norm
  set c₀ : ℝ := (Real.cosh (δ * a) - 1) * L / (π ^ 2 * a) with hc₀
  have hint2 : Integrable fun u =>
      ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ / 2 - c₀ * (cp u + cm u) :=
    (hEi.div_const 2).sub ((hcpi.add hcmi).const_mul c₀)
  have hmono : ∫ u, (edgeIntegrand L δ (EF.weilTest g g) u).re ≤ ∫ u,
      (‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ / 2 - c₀ * (cp u + cm u)) :=
    integral_mono hGi.re hint2
      (fun u => re_edgeIntegrand_le hL hδ ha haL hIm hcp0 hcm0 hcps hcms u)
  have hsplit : ∫ u, (‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ / 2 -
      c₀ * (cp u + cm u)) = (∫ u, ‖EF.weilTest g g u *
        ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖) / 2 - c₀ * (P ^ 2 + P ^ 2) := by
    have hA : Integrable fun u =>
        ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ / 2 := hEi.div_const 2
    have hB : Integrable fun u => c₀ * (cp u + cm u) := (hcpi.add hcmi).const_mul c₀
    rw [integral_sub hA hB, integral_div, integral_const_mul, integral_add hcpi hcmi, hcpm, hcmm]
  rw [hsplit] at hmono
  have hEint : ∫ u, ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ ≤
      2 * B * (2 * (Real.cosh (2 * δ * a) - 1)) * (4 * a) := by
    have hz' : ∀ u, u ∉ Icc (-(2 * a)) (2 * a) →
        ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖ = 0 := by
      intro u hu
      by_contra h
      exact hu (abs_le.mp (run_factor_support hK0 (fun h0 => h (by rw [h0, norm_zero]))).2)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz']
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(2 * a)) (2 * a))
      (f := fun u => ‖EF.weilTest g g u * ((2 * (Real.cosh (δ * u) - 1) : ℝ) : ℂ)‖)
      (C := 2 * B * (2 * (Real.cosh (2 * δ * a) - 1))) (by simp)
      (fun u _ => by rw [norm_norm]; exact norm_run_factor_le_cosh hδ ha.le hK0 hKn u)
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      show 2 * a - -(2 * a) = 4 * a by ring] at this
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at this)
  have hfar := Complex.abs_re_le_norm
    (paperFT (edgeIntegrand L δ (EF.weilTest g g)) ((2 * π / L * N : ℝ) : ℂ))
  have hre2 : ((2 : ℂ) * L * ((2 * B : ℝ) : ℂ)).re = 4 * L * B := by
    rw [show ((2 : ℂ) * L * ((2 * B : ℝ) : ℂ)) = ((4 * L * B : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hc2 : c₀ * (P ^ 2 + P ^ 2) = 2 * (Real.cosh (δ * a) - 1) * L * P ^ 2 / (π ^ 2 * a) := by
    rw [hc₀]; field_simp; ring
  rw [hre2]
  have := neg_abs_le (paperFT (edgeIntegrand L δ (EF.weilTest g g)) ((2 * π / L * N : ℝ) : ℂ)).re
  linarith

/-- **Edge visibility law.** If `cosh(δa) > 1 + 8π²`, one smooth test supported in `[-a, a]`
makes the Weil form negative for every run `1, …, N` in every background of density
`L ≥ L₀`, once `N ≥ N₀(L)`. The threshold depends only on `δa`: off-line runs of any depth `δ`
are visible at aperture `O(1/δ)`, independently of the height scale `L`. -/
theorem exists_re_W_runConfig_neg {δ a : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ha : 0 < a)
    (hcosh : 1 + 8 * π ^ 2 < Real.cosh (δ * a)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ (L : ℝ) (hL : 0 < L), L₀ ≤ L → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ((runConfig hL hδ hδ' (runSet 1 N)).W f f).re < 0 := by
  obtain ⟨g, P, B, cp, cm, hg, hgs, hgB, hB0, hBP, hPa, hIm, hcp0, hcm0, hcps, hcms, hcpi,
    hcmi, hcpm, hcmm⟩ := exists_edgeTest ha
  have hπ2 : 0 < π ^ 2 := by positivity
  set κ : ℝ := (Real.cosh (δ * a) - 1) / (2 * π ^ 2) - 4 with hκ
  have hκ0 : 0 < κ := by
    rw [hκ, sub_pos, lt_div_iff₀ (by positivity)]
    nlinarith
  set C₁ : ℝ := 8 * a * (Real.cosh (2 * δ * a) - 1) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ Real.cosh (2 * δ * a) - 1 := by linarith [Real.one_le_cosh (2 * δ * a)]
    positivity
  refine ⟨g, hg, hgs, max (8 * a) (2 * C₁ / κ), lt_max_of_lt_left (by positivity),
    fun L hL hL₀ => ?_⟩
  have h8 : 8 * a ≤ L := le_trans (le_max_left _ _) hL₀
  have hCL : 2 * C₁ ≤ κ * L := by
    have := le_trans (le_max_right _ _) hL₀
    rw [div_le_iff₀ hκ0] at this
    linarith
  have hP : 0 < P := by linarith
  have hε : 0 < κ * L * P / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (tendsto_paperFT_mul_nat
    (edgeIntegrand L δ (EF.weilTest g g)) (c := 2 * π / L) (by positivity))) _ hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hfar := hN₀ N hN
  rw [dist_zero_right] at hfar
  have hest := re_W_runConfig_le_edge hL hδ hδ' ha h8 hg hgs hgB hIm hcp0 hcm0 hcps hcms hcpi
    hcmi hcpm hcmm N
  have h1 : 4 * L * B ≤ 4 * L * P := by nlinarith
  have h2 : 8 * a * B * (Real.cosh (2 * δ * a) - 1) ≤ C₁ * P := by
    rw [hC₁]
    have : 0 ≤ Real.cosh (2 * δ * a) - 1 := by linarith [Real.one_le_cosh (2 * δ * a)]
    have : 0 ≤ 8 * a * (Real.cosh (2 * δ * a) - 1) := by positivity
    nlinarith
  have h3 : (κ + 4) * L * P ≤ 2 * (Real.cosh (δ * a) - 1) * L * P ^ 2 / (π ^ 2 * a) := by
    rw [hκ, sub_add_cancel, le_div_iff₀ (by positivity)]
    have hc : 0 ≤ Real.cosh (δ * a) - 1 := by linarith [Real.one_le_cosh (δ * a)]
    have : (Real.cosh (δ * a) - 1) / (2 * π ^ 2) * L * P * (π ^ 2 * a) =
        (Real.cosh (δ * a) - 1) * L * P * a / 2 := by field_simp
    rw [this]
    have hPP : P * a ≤ 4 * P ^ 2 := by nlinarith
    have : 0 ≤ (Real.cosh (δ * a) - 1) * L := by positivity
    nlinarith
  have h4 : C₁ * P ≤ κ * L * P / 2 := by nlinarith
  nlinarith

end GaloisForLFunctions.SquareRootThreshold
