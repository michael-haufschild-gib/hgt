import GaloisForLFunctions.SelbergClass.DegreeZeroContinuation
import GaloisForLFunctions.RHTower.CompletionOrderOneEnvelope
import GaloisForLFunctions.RHTower.PerronUniformFlankProducer

/-!
# Finite coefficient support in degree zero

Finite order supplies the strip growth needed by Phragmén–Lindelöf. The
degree-zero functional equation bounds the other flank by a conductor
exponential. Perron coefficient extraction then bounds the coefficient index.
No quiet-height assumption is supplied.
-/

noncomputable section
open Complex Filter Set Topology Asymptotics

namespace GaloisForLFunctions.SelbergClass

private theorem finiteOrder_strip_growth (E : RHTower.EntireFiniteOrder) :
    ∃ c < Real.pi / (2 - (-1)), ∃ D,
      (E : ℂ → ℂ) =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (-1) 2)]
        fun z => Real.exp (D * Real.exp (c * |z.im|)) := by
  obtain ⟨A, B, ρ, hA, _, _, hbound⟩ := E.growth
  let R := max 1 B
  let J (s : ℂ) := if R ≤ ‖s‖ then E s else 0
  have hJ : ∀ s : ℂ, ‖J s‖ ≤ A * Real.exp (‖s‖ ^ (ρ + 1)) := by
    intro s
    dsimp only [J]
    split_ifs with hs
    · have hr : 0 < ‖s‖ := lt_of_lt_of_le zero_lt_one ((le_max_left 1 B).trans hs)
      have hB : B ≤ ‖s‖ := (le_max_right 1 B).trans hs
      apply (hbound s).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hA.le
      rw [Real.rpow_add hr, Real.rpow_one]
      exact (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (norm_nonneg s) ρ)).trans_eq
        (mul_comm _ _)
    · simp only [norm_zero]
      positivity
  obtain ⟨c, hc, D, hD⟩ := RHTower.CompletionGrowth.isBigO_strip_of_finiteOrder hJ
  refine ⟨c, hc, D, ?_⟩
  have heq : (E : ℂ → ℂ) =ᶠ[comap (_root_.abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo (-1) 2)] J := by
    have hevent : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (-1) 2), R ≤ |z.im| :=
      ((eventually_ge_atTop R).comap (_root_.abs ∘ Complex.im)).filter_mono inf_le_left
    filter_upwards [hevent] with z hz
    exact (if_pos (hz.trans (Complex.abs_im_le_norm z))).symm
  exact heq.isBigO.trans hD

private theorem degreeZeroValue_norm_le_right (F : RHTower.ExtendedSelbergClass)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖degreeZeroValue F s‖ ≤ ∑' n, ‖LSeries.term F.coeff (2 : ℂ) n‖ := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [degreeZeroValue_eq F hs1]
  change ‖F.continuation.value s‖ ≤ _
  rw [← F.lSeries_eq_value s (by linarith)]
  have hb := F.lSeriesSummable (2 : ℂ) (by norm_num)
  have hbs := hb.of_re_le_re hs
  exact (norm_tsum_le_tsum_norm hbs.norm).trans
    (hbs.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re F.coeff hs) hb.norm)

private theorem degreeZeroValue_norm_le_left (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) {s : ℂ} (hs : s.re ≤ -1) :
    ‖degreeZeroValue F s‖ ≤ (∑' n, ‖LSeries.term F.coeff (2 : ℂ) n‖) *
      Real.exp (Real.log F.gammaData.Q * (1 - 2 * s.re)) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hr : 2 ≤ (1 - star s).re := by simpa using (by linarith : 2 ≤ 1 - s.re)
  have hr1 : 1 - star s ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [sub_re, one_re, RCLike.star_def, conj_re] at he
    linarith
  have hright := degreeZeroValue_norm_le_right F hr
  rw [degreeZeroValue_eq F hr1] at hright
  rw [degreeZeroValue_eq F hs1, degreeZero_functionalEquation F hF hs0 hs1,
    norm_mul, norm_star, norm_degreeZeroReflectionFactor F hF]
  exact (mul_le_mul_of_nonneg_left hright (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

/-- Finite order and the functional equation bound the whole central strip. -/
theorem degreeZeroValue_bounded_strip (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) :
    ∃ C : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖degreeZeroValue F s‖ ≤ C := by
  let B := ∑' n, ‖LSeries.term F.coeff (2 : ℂ) n‖
  let C := max B (B * Real.exp (Real.log F.gammaData.Q * 3))
  have hleft : ∀ s : ℂ, s.re = -1 → ‖degreeZeroValue F s‖ ≤ C := by
    intro s hs
    have h := degreeZeroValue_norm_le_left F hF hs.le
    simp only [hs] at h
    norm_num at h
    exact h.trans (le_max_right _ _)
  have hright : ∀ s : ℂ, s.re = 2 → ‖degreeZeroValue F s‖ ≤ C :=
    fun s hs => (degreeZeroValue_norm_le_right F hs.ge).trans (le_max_left _ _)
  have hdiff := analyticOnNhd_univ_iff_differentiable.mp (degreeZeroValue_analyticOnNhd F hF)
  exact ⟨C, fun s hs hs' => PhragmenLindelof.vertical_strip hdiff.diffContOnCl
    (finiteOrder_strip_growth (degreeZeroEntire F hF)) hleft hright hs hs'⟩

/-- The coefficient index is bounded by the conductor exponential. -/
theorem degreeZero_coefficient_index_le (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) {n : ℕ} (hn : F.coeff n ≠ 0) :
    (n : ℝ) ≤ Real.exp (2 * max (Real.log F.gammaData.Q) 0) := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  let B := ∑' j, ‖LSeries.term F.coeff (2 : ℂ) j‖
  let L := max (Real.log F.gammaData.Q) 0
  let R := Real.exp (2 * L)
  let H (M : ℕ) := (B * Real.exp L) * R ^ M
  have hB : 0 ≤ B := tsum_nonneg fun j => norm_nonneg _
  have hL : 0 ≤ L := le_max_right _ _
  have hflank : ∀ M : ℕ, ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - 2 →
      ‖degreeZeroValue F s‖ ≤ H M := by
    intro M s hs hs'
    have hexp : Real.log F.gammaData.Q * (1 - 2 * s.re) ≤ L * (1 + 2 * (M : ℝ)) := by
      calc Real.log F.gammaData.Q * (1 - 2 * s.re) ≤ L * (1 - 2 * s.re) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ L * (1 + 2 * (M : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hL
    calc ‖degreeZeroValue F s‖ ≤ B * Real.exp (Real.log F.gammaData.Q * (1 - 2 * s.re)) :=
        degreeZeroValue_norm_le_left F hF (by linarith)
      _ ≤ B * Real.exp (L * (1 + 2 * (M : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB
      _ = H M := by
        dsimp only [H, R]
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  obtain ⟨C, hC⟩ := degreeZeroValue_bounded_strip F hF
  let T (k : ℕ) : ℝ := 1 + k
  have hT : Tendsto T atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hTsq : Tendsto (fun k => T k ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hT.atTop_mul_atTop₀ hT
  apply RHTower.coefficient_index_le_exact_flank_radius_of_quiet_uniform_flank
    (F := degreeZeroValue F) (a := F.coeff) (c := 2) (H := H) (q := fun _ => C)
    (T := T) (C := B * Real.exp L) (R := R) (by norm_num)
    (analyticOnNhd_univ_iff_differentiable.mp (degreeZeroValue_analyticOnNhd F hF))
    (F.lSeriesSummable (2 : ℂ) (by norm_num))
    (fun s hs => by
      rw [degreeZeroValue_eq F (by intro h; simp [h] at hs)]
      exact (F.lSeries_eq_value s (by linarith)).symm)
    (Nat.one_le_iff_ne_zero.mpr hn0) hT
    (fun k σ hσ hσ' => by
      have hlo : -1 ≤ σ := by linarith
      exact ⟨hC _ (by simpa using hlo) (by simpa using hσ'),
        hC _ (by simpa using hlo) (by simpa using hσ')⟩)
    (Tendsto.div_atTop tendsto_const_nhds hTsq) hflank (Real.exp_nonneg _)
    (Eventually.of_forall fun _ => le_rfl) hn

/-- Degree zero forces finite Dirichlet support throughout the extended Selberg class. -/
theorem degreeZero_finite_support (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) : ∃ N : ℕ, ∀ n : ℕ, N < n → F.coeff n = 0 := by
  refine ⟨⌈Real.exp (2 * max (Real.log F.gammaData.Q) 0)⌉₊, fun n hn => ?_⟩
  by_contra hne
  have hle := (degreeZero_coefficient_index_le F hF hne).trans
    (Nat.le_ceil (Real.exp (2 * max (Real.log F.gammaData.Q) 0)))
  have : n ≤ ⌈Real.exp (2 * max (Real.log F.gammaData.Q) 0)⌉₊ := by exact_mod_cast hle
  omega

end GaloisForLFunctions.SelbergClass
