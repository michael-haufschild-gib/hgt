import GaloisForLFunctions.RHTower.EvenSectorSmoothTraceCorrection
import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundEnergy
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity

/-!
# An actual upward energy direction in the smooth even pole-free blind fibre

A sufficiently narrow three-bump pole cancellation is nonzero, even, smooth,
and invisible at every integer lag. Small-aperture positivity makes its
literal energy positive. Scalarization then raises energy within any exact
arithmetic fibre, with no limiting source or closure.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ContDiff
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided SeparatedBump

def smoothPolarBump (j : ℕ) : SmoothEvenPolarTestFn :=
  ⟨⟨⟨(fun x => (evenPolarProfile j x : ℂ)),
    Complex.ofRealCLM.contDiff.comp (contDiff_evenPolarProfile j),
    (SeparatedBump.hasCompactSupport_of_abs_gt (R := 6 * (nodeBump j).rOut / 2)
      (fun u hu => evenPolarProfile_eq_zero j hu)).comp_left Complex.ofReal_zero⟩,
    (fun x => by simp only [evenPolarProfile_neg]), paperFT_evenPolarProfile_I_div_two j⟩,
    Complex.ofRealCLM.contDiff.comp (contDiff_evenPolarProfile_infty j)⟩

theorem smoothPolarBump_zero (j : ℕ) : (smoothPolarBump j).1.1.1 0 = 1 := by
  have hr := (nodeBump j).rOut_pos
  change (evenPolarProfile j 0 : ℂ) = 1
  unfold evenPolarProfile
  rw [nodeBump_zero, nodeBump_eq_zero j (u := 0 - 2 * (nodeBump j).rOut)
      (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)]; linarith),
    nodeBump_eq_zero j (u := 0 + 2 * (nodeBump j).rOut)
      (by rw [zero_add, abs_of_pos (by positivity)]; linarith)]
  simp

theorem smoothPolarBump_tsupport (j : ℕ) :
    tsupport (smoothPolarBump j).1.1.1 ⊆
      Icc (-(3 * (nodeBump j).rOut)) (3 * (nodeBump j).rOut) := by
  change closure (Function.support (smoothPolarBump j).1.1.1) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply abs_le.mp
  by_contra hn
  have hz := evenPolarProfile_eq_zero j (u := x) (by linarith [lt_of_not_ge hn])
  exact hx (by change (evenPolarProfile j x : ℂ) = 0; rw [hz]; rfl)

theorem smoothPolarBump_blind (j : ℕ) (hj : 6 * (nodeBump j).rOut < Real.log 2) :
    logVector (smoothPolarBump j).1.1 = 0 := by
  have hs (x : ℝ) (hx : (smoothPolarBump j).1.1.1 x ≠ 0) :
      |x| ≤ 3 * (nodeBump j).rOut :=
    abs_le.mpr (smoothPolarBump_tsupport j (subset_tsupport _ hx))
  have hk := weilTest_support_abs_le hs hs
  ext n
  have hn : Real.log 2 ≤ Real.log (n : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast n.2)
  have hp : EF.weilTest (smoothPolarBump j).1.1.1 (smoothPolarBump j).1.1.1
      (Real.log (n : ℕ)) = 0 := by
    by_contra h
    have hh := hk _ h
    linarith [le_abs_self (Real.log (n : ℕ))]
  have hm : EF.weilTest (smoothPolarBump j).1.1.1 (smoothPolarBump j).1.1.1
      (-Real.log (n : ℕ)) = 0 := by
    by_contra h
    have hh := hk _ h
    rw [abs_neg] at hh
    linarith [le_abs_self (Real.log (n : ℕ))]
  simp only [logVector_apply, logValue, hp, hm, add_zero, Complex.zero_re,
    zero_div, Finsupp.zero_apply]

/-- A single smooth even pole-free source with zero whole arithmetic trace
and strictly positive actual archimedean energy. -/
theorem exists_positive_blind_smooth_source :
    ∃ f : SmoothEvenPolarTestFn, logVector f.1.1 = 0 ∧
      0 < weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) := by
  obtain ⟨δ, hδ, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  let a : SuzukiPositiveAperture := ⟨min (δ / 2) (Real.log 2 / 4),
    lt_min (by positivity) (by positivity)⟩
  have had : a.1 < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hal : 2 * a.1 < Real.log 2 := by
    have ha : a.1 ≤ Real.log 2 / 4 := min_le_right _ _
    linarith
  obtain ⟨j : ℕ, hj⟩ := exists_nat_gt (1 / a.1)
  have hja : 1 < (j : ℝ) * a.1 := (div_lt_iff₀ a.2).mp hj
  have hr : 3 * (nodeBump j).rOut < a.1 := by
    rw [nodeBump_rOut, mul_one_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [a.2]
  let f := smoothPolarBump j
  have hs : tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    have hh := smoothPolarBump_tsupport j hx
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  let u : CCMComplexSmoothInteriorSource a := ⟨f.1.1.1, f.2, f.1.1.2.2, hs⟩
  have hne : ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0 := by
    intro hz
    have hu := u.toCCMFormVector_physical_coeFn
    rw [hz] at hu
    have hae : (u : ℝ → ℂ) =ᵐ[volume] 0 :=
      hu.symm.trans (Lp.coeFn_zero ℂ 2 volume)
    have heq := (u.continuous.ae_eq_iff_eq volume continuous_zero).mp hae
    have h0 := congrFun heq 0
    change (smoothPolarBump j).1.1.1 0 = 0 at h0
    rw [smoothPolarBump_zero] at h0
    exact one_ne_zero h0
  have hQ : 0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector :=
    (mul_pos (hpos a had) (pow_pos (norm_pos_iff.mpr hne) 2)).trans_le
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u.toCCMFormVector)
  have hblind := smoothPolarBump_blind j (by linarith)
  refine ⟨f, hblind, ?_⟩
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil] at hQ
  change 0 < (zetaZeroConfig.W f.1.1.1 f.1.1.1).re at hQ
  rw [zeta_W_eq_weilFullFunctional f.1.1.2.1 f.1.1.2.2,
    re_weilFullFunctional_eq _ f.1.1, hblind, map_zero, sub_zero] at hQ
  exact hQ

/-- Every higher energy in a smooth source's exact trace fibre is realized
by one smooth source. The coefficient is an exact energy difference. -/
theorem exists_smooth_source_energy_raise (f : SmoothEvenPolarTestFn) {E : ℝ}
    (hE : weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) ≤ E) :
    ∃ g : SmoothEvenPolarTestFn, logVector g.1.1 = logVector f.1.1 ∧
      weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) = E := by
  classical
  obtain ⟨b, hb, hB⟩ := exists_positive_blind_smooth_source
  let A := weilArchRe (EF.weilTest f.1.1.1 f.1.1.1)
  let B := weilArchRe (EF.weilTest b.1.1.1 b.1.1.1)
  let t := (E - A) / B
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hE) hB.le
  let c := Finsupp.single f (1 : ℝ) + Finsupp.single b t
  have hc (g) : 0 ≤ c g := by
    simp only [c, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> positivity
  obtain ⟨g, _, hg, henergy⟩ := exists_smooth_scalarization_moments c hc
  refine ⟨g, hg.trans ?_, henergy.trans ?_⟩
  · simp only [c, smoothMixtureTrace, map_add, linearCombination_single,
      one_smul, hb, smul_zero, add_zero]
  · simp only [c, smoothMixtureEnergy, map_add, linearCombination_single,
      smul_eq_mul, one_mul]
    change A + (E - A) / B * B = E
    rw [div_mul_cancel₀ _ hB.ne']
    ring

end RHTower.EvenSector
