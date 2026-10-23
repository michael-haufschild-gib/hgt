import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding

/-!
# Bézout positivity on the scaling surface: distinct effective cycles meet nonnegatively

Call a cycle `f` of the scaling surface **effective** when it is a nonnegative real test, and two
effective cycles **without common component** when their supports are disjoint (`f · g ≡ 0`). On a
surface two effective divisors without common component meet nonnegatively; a self-intersection
can be negative. The scaling surface has this property unconditionally.

**The collar of two cycles** (`re_archCross_eq`). For real `C²` compactly supported `f, g` the
archimedean term of their local intersection is, by polarizing the Lévy–Khintchine form of the
archimedean symbol (`RHTower.integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner`),

    (1/2π) ∫ Re(f̂ ḡ̂) A = A(0) ∫ f g + ∫_0^∞ ω(x) ∫ (f(u) − f(u+x))(g(u) − g(u+x)) du dx,

with `ω(x) = e^{−x/2}/(1 − e^{−2x})`. Without common component the first term vanishes and the
jump integrand is `−(f(u)g(u+x) + f(u+x)g(u))` (`archCross_eq_neg_of_disjoint`).

**Theorem** (`localPair_eq_of_disjoint`, `localPair_nonneg`). For effective cycles `f, g` without
common component the local intersection is the sum of two positive kernels,

    f · g = Σ_n Λ(n) n^{−1/2} (k(log n) + k(−log n)) + ∫_0^∞ ω(x) ∫ (f(u)g(u+x) + f(u+x)g(u)) du dx,

`k = f ⋆ g̃ ≥ 0`: the prime incidence and the archimedean collar. Hence `f · g ≥ 0`.

So the Bézout half of the surface's positivity holds: effective cycles meet the fibres
nonnegatively (`f·H = ∫ f e^{−u/2} ≥ 0`, `f·V = ∫ f e^{u/2} ≥ 0`) and each other nonnegatively
when they have no common component. What the Hodge index needs beyond Bézout is the
Riemann–Roch axiom, a supply of effective cycles in every class of positive square, and that is
the open core. The self-intersection of an effective cycle is not controlled: it contains
`A(0)‖f‖² < 0`, the arithmetic genus term.
-/

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {f g : ℝ → ℝ}

/-- A continuous compactly supported real function is integrable. -/
theorem integrable_of_cs {φ : ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable φ :=
  hc.integrable_of_hasCompactSupport hs

theorem hasCompactSupport_sq {φ : ℝ → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport fun u => φ u ^ 2 := by
  rw [hasCompactSupport_iff_eventuallyEq] at hs ⊢
  filter_upwards [hs] with u hu
  simp [hu]

theorem hasCompactSupport_shiftDiff {φ : ℝ → ℝ} (hs : HasCompactSupport φ) (x : ℝ) :
    HasCompactSupport fun u => φ u - φ (u + x) :=
  hs.sub (hs.comp_homeomorph (Homeomorph.addRight x))

/-- The archimedean spectral weight of a real `C²` compactly supported test is integrable. -/
theorem integrable_normSq_paperFT_mul_gammaBracket {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    Integrable fun r : ℝ => ‖paperFT (fun u => (φ u : ℂ)) r‖ ^ 2 * EF.gammaBracket r := by
  set Φ : ℝ → ℂ := fun u => (φ u : ℂ)
  have hΦc : Continuous Φ := Complex.continuous_ofReal.comp hφ.continuous
  have hΦs : HasCompactSupport Φ := hφc.comp_left Complex.ofReal_zero
  have hΦ2 : ContDiff ℝ 2 Φ := Complex.ofRealCLM.contDiff.comp hφ
  have hk : ∀ r : ℝ, paperFT (EF.weilTest Φ Φ) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT Φ r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest hΦc hΦc hΦs hΦs, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  refine (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hΦ2 hΦs hΦ2 hΦs).re.congr
    (Eventually.of_forall fun r => ?_)
  change (paperFT (EF.weilTest Φ Φ) r * (EF.gammaBracket r : ℂ)).re = _
  rw [hk r, Complex.ofReal_re]

/-- **The collar of two cycles in jump form**, by polarization of the Lévy–Khintchine form. -/
theorem re_archCross_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
        ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x))) (Ioi 0) ∧
      (1 / (2 * Real.pi)) * ∫ r : ℝ, (paperFT (fun u => (f u : ℂ)) r *
          conj (paperFT (fun u => (g u : ℂ)) r)).re * EF.gammaBracket r =
        EF.gammaBracket 0 * (∫ u, f u * g u) +
          ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x)) := by
  set F : ℝ → ℂ := fun u => (f u : ℂ)
  set G : ℝ → ℂ := fun u => (g u : ℂ)
  have hf1 := integrable_of_cs hf.continuous hfc
  have hg1 := integrable_of_cs hg.continuous hgc
  set gP : ℝ → ℝ := fun u => f u + g u
  set gM : ℝ → ℝ := fun u => f u - g u
  have hgP : ContDiff ℝ 2 gP := hf.add hg
  have hgM : ContDiff ℝ 2 gM := hf.sub hg
  have hgPc : HasCompactSupport gP := hfc.add hgc
  have hgMc : HasCompactSupport gM := hfc.sub hgc
  have hint_f := integrable_normSq_paperFT_mul_gammaBracket hf hfc
  have hint_g := integrable_normSq_paperFT_mul_gammaBracket hg hgc
  have hint_P := integrable_normSq_paperFT_mul_gammaBracket hgP hgPc
  have hint_M := integrable_normSq_paperFT_mul_gammaBracket hgM hgMc
  -- pointwise polarization of the spectral weights
  have hpol : ∀ r : ℝ,
      ‖paperFT (fun u => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
          ‖paperFT (fun u => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r =
        4 * ((paperFT F r * conj (paperFT G r)).re * EF.gammaBracket r) := fun r => by
    obtain ⟨hP, hM⟩ := paperFT_ofReal_add_and_sub hf1 hg1 r
    obtain ⟨hnP, hnM⟩ := norm_add_and_sub_sq_eq (paperFT F r) (paperFT G r)
    simp only [gP, gM]
    rw [hP, hM, hnP, hnM]
    ring
  obtain ⟨hOnP, hbP⟩ := integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hgP.continuous
    (integrable_of_cs hgP.continuous hgPc)
    (integrable_of_cs (hgP.continuous.pow 2) (hasCompactSupport_sq hgPc)) hint_P
  obtain ⟨hOnM, hbM⟩ := integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hgM.continuous
    (integrable_of_cs hgM.continuous hgMc)
    (integrable_of_cs (hgM.continuous.pow 2) (hasCompactSupport_sq hgMc)) hint_M
  -- the shift integrals polarize
  have hshift : ∀ x : ℝ, (∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x))) =
      (1 / 4 : ℝ) * ((∫ u : ℝ, (gP u - gP (u + x)) ^ 2) - ∫ u : ℝ, (gM u - gM (u + x)) ^ 2) := by
    intro x
    have hc : ∀ φ : ℝ → ℝ, Continuous φ → Continuous fun u => φ u - φ (u + x) := fun φ hφ =>
      hφ.sub (hφ.comp (continuous_id.add continuous_const))
    have hiP := integrable_of_cs ((hc gP hgP.continuous).pow 2)
      (hasCompactSupport_sq (hasCompactSupport_shiftDiff hgPc x))
    have hiM := integrable_of_cs ((hc gM hgM.continuous).pow 2)
      (hasCompactSupport_sq (hasCompactSupport_shiftDiff hgMc x))
    rw [← integral_sub hiP hiM, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [gP, gM]
    ring
  have hint_cross : IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x))) (Ioi 0) := by
    refine ((hOnP.sub hOnM).const_mul (1 / 4 : ℝ)).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [hshift x]
    ring
  refine ⟨hint_cross, ?_⟩
  have hsq : (∫ u, gP u ^ 2) - ∫ u, gM u ^ 2 = 4 * ∫ u, f u * g u := by
    rw [← integral_sub (integrable_of_cs (hgP.continuous.pow 2) (hasCompactSupport_sq hgPc))
      (integrable_of_cs (hgM.continuous.pow 2) (hasCompactSupport_sq hgMc)),
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [gP, gM]
    ring
  have hlev : (∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (gP u - gP (u + x)) ^ 2) -
      (∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (gM u - gM (u + x)) ^ 2) =
      4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        ∫ u : ℝ, (f u - f (u + x)) * (g u - g (u + x)) := by
    rw [← integral_sub hOnP hOnM, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only
    rw [hshift x]
    ring
  have hspec : (1 / (2 * Real.pi)) * ∫ r : ℝ, (paperFT F r * conj (paperFT G r)).re *
      EF.gammaBracket r = (1 / 4) * ((1 / (2 * Real.pi)) *
        (∫ r : ℝ, ‖paperFT (fun u => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
      (1 / (2 * Real.pi)) *
        (∫ r : ℝ, ‖paperFT (fun u => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r)) := by
    rw [← mul_sub, ← integral_sub hint_P hint_M]
    have : (∫ r : ℝ, ‖paperFT (fun u => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (fun u => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) =
        4 * ∫ r : ℝ, (paperFT F r * conj (paperFT G r)).re * EF.gammaBracket r := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hpol)
    rw [this]
    ring
  rw [hspec, hbP, hbM]
  linear_combination (1 / 4 : ℝ) * EF.gammaBracket 0 * hsq + (1 / 4 : ℝ) * hlev

/-- **Without common component** the collar is `−∫_0^∞ ω(x) ∫ (f(u)g(u+x) + f(u+x)g(u))`. -/
theorem archCross_eq_neg_of_disjoint (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hfg : ∀ u, f u * g u = 0) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ, (paperFT (fun u => (f u : ℂ)) r *
        conj (paperFT (fun u => (g u : ℂ)) r)).re * EF.gammaBracket r =
      -∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (f u * g (u + x) + f (u + x) * g u) := by
  rw [(re_archCross_eq hf hfc hg hgc).2, show (∫ u, f u * g u) = 0 by simp [hfg],
    mul_zero, zero_add, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only
  rw [← mul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have h1 := hfg u
  have h2 := hfg (u + x)
  simp only
  linear_combination h1 + h2

/-- The local intersection of two tests. -/
def localPair (f g : ℝ → ℂ) : ℂ := localGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ![f, g] 0 1

/-- The autocorrelation of two nonnegative real tests is nonnegative and real. -/
theorem re_weilTest_nonneg (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) (x : ℝ) :
    0 ≤ (EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) x).re := by
  have he : EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) x =
      ((∫ t, f t * g (t - x) : ℝ) : ℂ) := by
    rw [EF.weilTest, convolution_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.mul_apply', EF.tilde, Complex.conj_ofReal, neg_sub]
    push_cast
    ring
  rw [he, Complex.ofReal_re]
  exact integral_nonneg fun t => mul_nonneg (hf0 t) (hg0 _)

/-- **The local intersection of effective cycles without common component**: prime incidence
plus archimedean collar. -/
theorem localPair_eq_of_disjoint (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hfg : ∀ u, f u * g u = 0) :
    (localPair (fun u => (f u : ℂ)) (fun u => (g u : ℂ))).re =
      (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (Real.log n) +
          EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (-Real.log n))).re +
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (f u * g (u + x) + f (u + x) * g u) := by
  set F : ℝ → ℂ := fun u => (f u : ℂ)
  set G : ℝ → ℂ := fun u => (g u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hGc : Continuous G := Complex.continuous_ofReal.comp hg.continuous
  have hFs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hGs : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hG2 : ContDiff ℝ 2 G := Complex.ofRealCLM.contDiff.comp hg
  have hfam : ∀ i, Continuous (![F, G] i) := fun i => by fin_cases i <;> assumption
  have hfamc : ∀ i, HasCompactSupport (![F, G] i) := fun i => by fin_cases i <;> assumption
  have hloc := localGram_apply (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ![F, G] hfam
    hfamc 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hloc
  -- the archimedean integral is real on the real line
  have hint := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFs hG2 hGs
  have hre : (∫ r : ℝ, paperFT (EF.weilTest F G) r * (EF.gammaBracket r : ℂ)).re =
      ∫ r : ℝ, (paperFT F r * conj (paperFT G r)).re * EF.gammaBracket r := by
    rw [← integral_re hint]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [EF.paperFT_weilTest hFc hGc hFs hGs, Complex.conj_ofReal, Complex.re_mul_ofReal]
  have hconst : ((1 / (2 * Real.pi) : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
  rw [localPair, hloc, Complex.sub_re, hconst, Complex.re_ofReal_mul, hre,
    archCross_eq_neg_of_disjoint hf hfc hg hgc hfg]
  ring

/-- **Bézout positivity.** Two effective cycles of the scaling surface without common component
meet nonnegatively. -/
theorem localPair_nonneg (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    (hfg : ∀ u, f u * g u = 0) :
    0 ≤ (localPair (fun u => (f u : ℂ)) (fun u => (g u : ℂ))).re := by
  rw [localPair_eq_of_disjoint hf hfc hg hgc hfg]
  refine add_nonneg ?_ (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  · set a : ℕ → ℂ := fun n =>
      ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (Real.log n) +
          EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (-Real.log n))
    have ha : ∀ n, 0 ≤ (a n).re := fun n => by
      simp only [a]
      rw [Complex.re_ofReal_mul, Complex.add_re]
      refine mul_nonneg ?_ (add_nonneg (re_weilTest_nonneg hf0 hg0 _) (re_weilTest_nonneg hf0 hg0 _))
      split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      · exact le_rfl
    by_cases hs : Summable a
    · rw [Complex.re_tsum hs]
      exact tsum_nonneg ha
    · rw [tsum_eq_zero_of_not_summable hs, Complex.zero_re]
  · exact mul_nonneg (archLevyDensity_pos hx).le
      (integral_nonneg fun u => add_nonneg (mul_nonneg (hf0 u) (hg0 _)) (mul_nonneg (hf0 _) (hg0 u)))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
