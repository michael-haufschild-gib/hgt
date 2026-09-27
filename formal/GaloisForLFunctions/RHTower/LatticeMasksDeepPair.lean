import GaloisForLFunctions.RHTower.SubNyquistHodgeExclusion
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# A dense critical lattice masks an isolated deep pair

The doubled critical lattice `{½ + 2πik/L}` together with one off-line pair `½ ± δ + iγ*`
(`latticeWithPairConfig`) has Weil form `2L⟨f, g⟩` plus the two summands of the pair on tests
supported in `[-L/2, L/2]` (`W_latticeWithPairConfig`, from the Poisson computation of
`ZeroLatticeDepthNyquistLaw`).  By Cauchy–Schwarz the pair costs at most `2 · 2a e^{2aδ} ∫|f|²` on
tests supported in `[-a, a]` (`norm_paperFT_sq_le`), so the Weil form is nonnegative as soon as
`2a e^{2aδ} ≤ L` (`re_W_latticeWithPairConfig_nonneg`).

This is the density half of the masking dichotomy of `FiniteLevelResolutionLaw`
(`lattice_masks_isolated_deep_pair`): with local count `A₀ ≍ L`, an isolated zero of depth `δ` is
invisible to the level-`a` Hodge index up to `δ a ≈ ½ log(L/2a)`.  The law
`δ a < 12((4 n_δ + 2) log(10⁶/δ) + log(A₀ log(|γ| + 3)) + 18)` there has `n_δ = 2` for this
configuration, so its density term `log A₀` is necessary up to the constant.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### The size of a transform off the real axis -/

/-- For a test supported in `[-a, a]`, `|f̂(z)|² ≤ 2a e^{2a|Im z|} ∫ |f|²`. -/
theorem norm_paperFT_sq_le {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) (z : ℂ) :
    ‖paperFT f z‖ ^ 2 ≤ 2 * a * Real.exp (2 * a * |z.im|) * ∫ t, ‖f t‖ ^ 2 := by
  have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_tsupport f) hfs
  have hzero : ∀ t, t ∉ Icc (-a) a → f t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => ht (hfs h))
  -- the pointwise bound
  have hpt : ∀ t, ‖f t * cexp (I * z * t)‖ ≤ Real.exp (a * |z.im|) * ‖f t‖ := by
    intro t
    rw [norm_mul, Complex.norm_exp, mul_comm]
    by_cases ht : t ∈ Icc (-a) a
    · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have : (I * z * (t : ℂ)).re = -(z.im * t) := by simp [Complex.mul_re]
      rw [this]
      have h1 : |t| ≤ a := abs_le.mpr ht
      have h2 := neg_abs_le (z.im * t)
      rw [abs_mul] at h2
      nlinarith [abs_nonneg z.im, abs_nonneg t]
    · rw [hzero t ht, norm_zero, mul_zero, mul_zero]
  have hint1 : Integrable (fun t => ‖f t‖) := (hf.norm.integrable_of_hasCompactSupport hfc.norm)
  have hbound : ‖paperFT f z‖ ≤ Real.exp (a * |z.im|) * ∫ t, ‖f t‖ := by
    rw [paperFT_def]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      (hint1.const_mul _) (Eventually.of_forall hpt)
  -- Cauchy–Schwarz on `[-a, a]`
  have hc2 : HasCompactSupport (fun t => ‖f t‖ ^ 2) := by
    have h := (hfc.norm).mul_right (f' := fun t => ‖f t‖)
    have e : (fun t => ‖f t‖ ^ 2) = fun t => ‖f t‖ * ‖f t‖ := funext fun t => sq _
    rw [e]; exact h
  have hsq2 : Integrable (fun t => ‖f t‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hc2
  have hrestrict1 : ∫ t, ‖f t‖ = ∫ t in Icc (-a) a, ‖f t‖ * 1 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-a) a)
      (fun t ht => by rw [hzero t ht, norm_zero])]
    simp
  have hrestrict2 : ∫ t in Icc (-a) a, ‖f t‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by rw [hzero t ht]; simp)
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := volume.restrict (Icc (-a) a)) (f := fun t => ‖f t‖) (g := fun _ => (1 : ℝ))
    hf.norm.aestronglyMeasurable aestronglyMeasurable_const hsq2.integrableOn
    (by simp)
  have hvol : ∫ _t in Icc (-a) a, (1 : ℝ) ^ 2 = 2 * a := by
    simp [Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]
    ring
  rw [hvol, hrestrict2, ← hrestrict1] at hcs
  have hI0 : 0 ≤ ∫ t, ‖f t‖ := integral_nonneg fun t => norm_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  calc ‖paperFT f z‖ ^ 2 ≤ (Real.exp (a * |z.im|) * ∫ t, ‖f t‖) ^ 2 := hsq
    _ = Real.exp (2 * a * |z.im|) * (∫ t, ‖f t‖) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    _ ≤ Real.exp (2 * a * |z.im|) * ((∫ t, ‖f t‖ ^ 2) * (2 * a)) :=
        mul_le_mul_of_nonneg_left hcs (Real.exp_pos _).le
    _ = 2 * a * Real.exp (2 * a * |z.im|) * ∫ t, ‖f t‖ ^ 2 := by ring

/-! ### The configuration -/

/-- The off-line pair `½ ± δ + iγ*`. -/
def deepPairPoint (δ γs : ℝ) (b : Bool) : ℂ := if b then ⟨1 / 2 + δ, γs⟩ else ⟨1 / 2 - δ, γs⟩

theorem deepPairPoint_injective {δ : ℝ} (hδ : 0 < δ) (γs : ℝ) :
    Function.Injective (deepPairPoint δ γs) := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [deepPairPoint, Complex.ext_iff] <;> linarith

/-- The doubled critical lattice `{½ + 2πik/L}` together with one off-line pair `½ ± δ + iγ*`:
multiplicity two on the critical line, one off it. -/
def latticeWithPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γs : ℝ) :
    ZeroConfig where
  carrier := Set.range (verticalLatticePoint L 0) ∪ Set.range (deepPairPoint δ γs)
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨b, rfl⟩)
    · simp only [verticalLatticePoint]; norm_num
    · cases b <;> simp only [deepPairPoint] <;> constructor <;> norm_num <;> linarith
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨b, rfl⟩)
    · exact Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩
    · refine Or.inr ⟨!b, ?_⟩
      cases b
      · apply Complex.ext
        · rw [reflect_re']; simp [deepPairPoint]; ring
        · rw [reflect_im']; simp [deepPairPoint]
      · apply Complex.ext
        · rw [reflect_re']; simp [deepPairPoint]; ring
        · rw [reflect_im']; simp [deepPairPoint]
  mult_reflect := by
    intro ρ _
    simp only [reflect_re']
    have : (1 - ρ.re = 1 / 2) ↔ (ρ.re = 1 / 2) := by constructor <;> intro h <;> linarith
    simp only [this]
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    refine ((hF.image (verticalLatticePoint L 0)).union
      ((Set.finite_range (deepPairPoint δ γs)))).subset ?_
    rintro _ ⟨⟨k, rfl⟩ | ⟨b, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

/-- **The Weil form.**  For tests supported in `[-L/2, L/2]`, the Weil form is `2L⟨f, g⟩` plus
the two summands of the pair. -/
theorem W_latticeWithPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γs : ℝ)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    (latticeWithPairConfig hL hδ hδ' γs).W f g =
      2 * L * (∫ t, f t * conj (g t)) +
        ((latticeWithPairConfig hL hδ hδ' γs).Wsummand f g (deepPairPoint δ γs true) +
          (latticeWithPairConfig hL hδ hδ' γs).Wsummand f g (deepPairPoint δ γs false)) := by
  set Z := latticeWithPairConfig hL hδ hδ' γs with hZ
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hK := EF.weilTest_contDiff hf hg hfc
  have hKs := weilTest_abs_le hfs hgs
  have hdisj : Disjoint (Set.range (verticalLatticePoint L 0))
      (Set.range (deepPairPoint δ γs)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨b, hb⟩
    have := congrArg Complex.re hb
    cases b <;> simp [verticalLatticePoint, deepPairPoint] at this <;> linarith
  have h₁ : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => Z.Wsummand f g ρ)
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
    simp [hZ, latticeWithPairConfig, verticalLatticePoint]
  have h₂ : HasSum (fun ρ : Set.range (deepPairPoint δ γs) => Z.Wsummand f g ρ)
      (Z.Wsummand f g (deepPairPoint δ γs true) + Z.Wsummand f g (deepPairPoint δ γs false)) := by
    rw [(deepPairPoint_injective hδ γs).hasSum_range_iff]
    have h := hasSum_fintype (fun b : Bool => Z.Wsummand f g (deepPairPoint δ γs b))
    rw [Fintype.sum_bool] at h
    exact h
  have hl := tsum_weilTest_lattice_eq hL hf hg hfs hgs (fun _ => 1) rfl
  simp only [mul_one] at hl
  have hW : Z.W f g = 2 * (L * ∑' m : ℤ, EF.weilTest f g (m * L)) +
      (Z.Wsummand f g (deepPairPoint δ γs true) + Z.Wsummand f g (deepPairPoint δ γs false)) :=
    (HasSum.add_disjoint (f := Z.Wsummand f g) hdisj h₁ h₂).tsum_eq
  rw [hW, hl]
  ring

/-! ### Positivity below the density level -/

theorem re_integral_mul_conj_self (f : ℝ → ℂ) :
    (∫ t, f t * conj (f t)).re = ∫ t, ‖f t‖ ^ 2 := by
  have h : (fun t => f t * conj (f t)) = fun t => ((‖f t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal, Complex.ofReal_re]

/-- The summand of an off-line point `½ + ε + iγ*` is at most `2a e^{2a|ε|} ∫|f|²`. -/
theorem norm_Wsummand_pair_le (Z : ZeroConfig) {f : ℝ → ℂ} {a ε γs : ℝ} (ha : 0 ≤ a)
    (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) (hm : Z.mult ⟨1 / 2 + ε, γs⟩ = 1) :
    ‖Z.Wsummand f f ⟨1 / 2 + ε, γs⟩‖ ≤ 2 * a * Real.exp (2 * a * |ε|) * ∫ t, ‖f t‖ ^ 2 := by
  have hg := gammaOf_sub_of_re_im (ρ := (⟨1 / 2 + ε, γs⟩ : ℂ)) (γ₀ := γs) rfl rfl
  obtain ⟨h1, h2⟩ := hg
  have e1 : gammaOf (⟨1 / 2 + ε, γs⟩ : ℂ) = γs - I * ε := by linear_combination h1
  have e2 : conj ((γs : ℂ) - I * ε) = γs + I * ε := by
    rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  set B := 2 * a * Real.exp (2 * a * |ε|) * ∫ t, ‖f t‖ ^ 2 with hB
  have hb1 := norm_paperFT_sq_le ha hf hfs ((γs : ℂ) - I * ε)
  have hb2 := norm_paperFT_sq_le ha hf hfs ((γs : ℂ) + I * ε)
  have hi1 : |((γs : ℂ) - I * ε).im| = |ε| := by simp
  have hi2 : |((γs : ℂ) + I * ε).im| = |ε| := by simp
  rw [hi1] at hb1
  rw [hi2] at hb2
  rw [ZeroConfig.Wsummand, hm, e1, e2, Nat.cast_one, one_mul, norm_mul, Complex.norm_conj]
  have hx := norm_nonneg (paperFT f ((γs : ℂ) - I * ε))
  have hy := norm_nonneg (paperFT f ((γs : ℂ) + I * ε))
  nlinarith [sq_nonneg (‖paperFT f ((γs : ℂ) - I * ε)‖ - ‖paperFT f ((γs : ℂ) + I * ε)‖)]

/-- **Density masking.**  If `a ≤ L/2` and `2a e^{2aδ} ≤ L`, the doubled critical lattice of
spacing `2π/L` with the pair `½ ± δ + iγ*` has nonnegative Weil form on every `C²` test supported in
`[-a, a]`. -/
theorem re_W_latticeWithPairConfig_nonneg {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γs : ℝ) (ha : 0 ≤ a) (haL : a ≤ L / 2)
    (hmask : 2 * a * Real.exp (2 * a * δ) ≤ L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((latticeWithPairConfig hL hδ hδ' γs).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) haL)
  rw [W_latticeWithPairConfig hL hδ hδ' γs hf hf.continuous hfs' hfs']
  have hmP : (latticeWithPairConfig hL hδ hδ' γs).mult ⟨1 / 2 + δ, γs⟩ = 1 := by
    show (if (⟨1 / 2 + δ, γs⟩ : ℂ).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg]; simp only; linarith
  have hmM : (latticeWithPairConfig hL hδ hδ' γs).mult ⟨1 / 2 + -δ, γs⟩ = 1 := by
    show (if (⟨1 / 2 + -δ, γs⟩ : ℂ).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg]; simp only; linarith
  have hbP := norm_Wsummand_pair_le (latticeWithPairConfig hL hδ hδ' γs) ha hf.continuous hfs hmP
  have hbM := norm_Wsummand_pair_le (latticeWithPairConfig hL hδ hδ' γs) ha hf.continuous hfs hmM
  rw [abs_of_pos hδ] at hbP
  rw [abs_neg, abs_of_pos hδ] at hbM
  have eP : deepPairPoint δ γs true = ⟨1 / 2 + δ, γs⟩ := rfl
  have eM : deepPairPoint δ γs false = ⟨1 / 2 + -δ, γs⟩ := by
    simp only [deepPairPoint]; apply Complex.ext <;> simp; ring
  rw [eP, eM, Complex.add_re, Complex.add_re]
  set E := ∫ t, ‖f t‖ ^ 2 with hE
  have hE0 : 0 ≤ E := integral_nonneg fun t => sq_nonneg _
  have hmain : (2 * (L : ℂ) * ∫ t, f t * conj (f t)).re = 2 * L * E := by
    rw [show (2 * (L : ℂ)) = ((2 * L : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      re_integral_mul_conj_self]
  rw [hmain]
  have aP := Complex.abs_re_le_norm ((latticeWithPairConfig hL hδ hδ' γs).Wsummand f f
    ⟨1 / 2 + δ, γs⟩)
  have aM := Complex.abs_re_le_norm ((latticeWithPairConfig hL hδ hδ' γs).Wsummand f f
    ⟨1 / 2 + -δ, γs⟩)
  have nP := neg_abs_le ((latticeWithPairConfig hL hδ hδ' γs).Wsummand f f ⟨1 / 2 + δ, γs⟩).re
  have nM := neg_abs_le ((latticeWithPairConfig hL hδ hδ' γs).Wsummand f f ⟨1 / 2 + -δ, γs⟩).re
  have hkey : 2 * (2 * a * Real.exp (2 * a * δ) * E) ≤ 2 * L * E := by nlinarith
  linarith

/-! ### The masking configuration -/

/-- Every unit window carries at most `L/π + 6` zeros, with multiplicity. -/
theorem latticeWithPairConfig_N_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γs t : ℝ) : ((latticeWithPairConfig hL hδ hδ' γs).N t (t + 1) : ℝ) ≤ L / π + 6 := by
  classical
  set Z := latticeWithPairConfig hL hδ hδ' γs with hZ
  set K := {k : ℤ | t < (k : ℝ) * (2 * π / L) ∧ (k : ℝ) * (2 * π / L) ≤ t + 1} with hK
  have hh : 0 < 2 * π / L := by positivity
  have hKfin : K.Finite := finite_latticeWindow hh t (t + 1)
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  have hmult : ∀ ρ, Z.mult ρ ≤ 2 := fun ρ => by
    show (if ρ.re = 1 / 2 then 2 else 1) ≤ 2
    split_ifs <;> norm_num
  have hN : Z.N t (t + 1) ≤ 2 * (Z.window t (t + 1)).ncard := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
    calc ∑ ρ ∈ hfin.toFinset, Z.mult ρ ≤ ∑ _ρ ∈ hfin.toFinset, 2 :=
          Finset.sum_le_sum fun ρ _ => hmult ρ
      _ = 2 * hfin.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsub : Z.window t (t + 1) ⊆
      verticalLatticePoint L 0 '' K ∪ Set.range (deepPairPoint δ γs) := by
    rintro _ ⟨⟨k, rfl⟩ | ⟨b, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  have hpair : (Set.range (deepPairPoint δ γs)).ncard ≤ 2 := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
  have h1 : (Z.window t (t + 1)).ncard ≤ K.ncard + 2 := by
    refine (Set.ncard_le_ncard hsub ((hKfin.image _).union (Set.finite_range _))).trans ?_
    refine (Set.ncard_union_le _ _).trans ?_
    have := Set.ncard_image_le (f := verticalLatticePoint L 0) hKfin
    omega
  have h2 := ncard_latticeWindow_le hh t
  have e : 1 / (2 * π / L) = L / (2 * π) := by field_simp
  rw [e] at h2
  calc (Z.N t (t + 1) : ℝ) ≤ 2 * ((Z.window t (t + 1)).ncard : ℝ) := by exact_mod_cast hN
    _ ≤ 2 * ((K.ncard : ℝ) + 2) := by gcongr; exact_mod_cast h1
    _ ≤ 2 * (L / (2 * π) + 1 + 2) := by gcongr
    _ = L / π + 6 := by field_simp; ring

/-- **A dense critical lattice masks an isolated deep pair.**  For `L > 0`, `0 < δ ≤ ½` and any
height `γ*`, the doubled critical lattice of spacing `2π/L` together with the pair `½ ± δ + iγ*`:

* has local count `N(t, t+1] ≤ (L/π + 6) log(|t| + 3)`;
* has the zero `½ + δ + iγ*`, and no other zero off the critical line except `½ - δ + iγ*`;
* satisfies the level-`a` Hodge index whenever `a ≤ L/2` and `2a e^{2aδ} ≤ L`.

So a deep zero isolated among critical zeros of density `L/2π` is invisible up to
`δ a ≈ ½ log(L/2a)`, and the term `log(A₀ log |γ|)` of `resolution_law_of_hodgeIndex` cannot be
removed. -/
theorem lattice_masks_isolated_deep_pair {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γs : ℝ) :
    (∀ t : ℝ, ((latticeWithPairConfig hL hδ hδ' γs).N t (t + 1) : ℝ) ≤
        (L / π + 6) * Real.log (|t| + 3)) ∧
      (⟨1 / 2 + δ, γs⟩ : ℂ) ∈ (latticeWithPairConfig hL hδ hδ' γs).carrier ∧
      (∀ ρ ∈ (latticeWithPairConfig hL hδ hδ' γs).carrier,
        ρ.re = 1 / 2 ∨ ρ = ⟨1 / 2 + δ, γs⟩ ∨ ρ = ⟨1 / 2 - δ, γs⟩) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ L / 2 → 2 * a * Real.exp (2 * a * δ) ≤ L →
        HodgeIndexAtLevel (latticeWithPairConfig hL hδ hδ' γs) a := by
  refine ⟨fun t => ?_, Or.inr ⟨true, rfl⟩, ?_, fun a ha haL hmask f hf hfs _ _ =>
    re_W_latticeWithPairConfig_nonneg hL hδ hδ' γs ha haL hmask hf hfs⟩
  · have h := latticeWithPairConfig_N_le hL hδ hδ' γs t
    have hlog : 1 ≤ Real.log (|t| + 3) := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      have := Real.exp_one_lt_d9
      linarith [abs_nonneg t]
    have : 0 ≤ L / π + 6 := by positivity
    nlinarith
  · rintro _ (⟨k, rfl⟩ | ⟨b, rfl⟩)
    · left; simp [verticalLatticePoint]
    · right; cases b
      · right; rfl
      · left; rfl

end RHTower
