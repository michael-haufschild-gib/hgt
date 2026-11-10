import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfAQuadraticRingPairsWithItsConductor
import GaloisForLFunctions.ExceptionalLayerTheory.TheDeuringHeilbronnRepulsionLaw
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw
import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt

/-!
# The exceptional square repels the other twisted squares

The logarithmic Deuring–Heilbronn margin bounds the transverse depth of
every remaining zero. Its hyperbolic energy bounds the negative part of
the actual square in the twisted explicit formula, including central zeros.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate
namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The sharp negative energy of a square at depth `δ`; the integral also
handles depth zero without a removable-singularity convention. -/
def squareDepthEnergy (δ a : ℝ) : ℝ :=
  ∫ u in Icc (-a) a, Real.sinh (δ * u) ^ 2

theorem squareDepthEnergy_nonneg (δ a : ℝ) : 0 ≤ squareDepthEnergy δ a :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

@[simp] theorem squareDepthEnergy_zero (a : ℝ) : squareDepthEnergy 0 a = 0 := by
  simp only [squareDepthEnergy, zero_mul, Real.sinh_zero, zero_pow (by norm_num : 2 ≠ 0), integral_zero]

theorem squareDepthEnergy_eq_pairEnergy {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    squareDepthEnergy δ a = SquareRootThreshold.pairEnergy δ a :=
  SquareRootThreshold.integral_sinh_sq_Icc hδ ha

/-- The negative-square energy increases with the absolute transverse depth. -/
theorem squareDepthEnergy_mono {δ Δ a : ℝ} (hδ : |δ| ≤ |Δ|) :
    squareDepthEnergy δ a ≤ squareDepthEnergy Δ a := by
  apply setIntegral_mono_on
    ((by fun_prop : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2).integrableOn_Icc)
    ((by fun_prop : Continuous fun u : ℝ => Real.sinh (Δ * u) ^ 2).integrableOn_Icc)
    measurableSet_Icc
  intro u _
  apply ZeroConfigurationGeometry.sinh_sq_le_sinh_sq
  simpa only [abs_mul] using mul_le_mul_of_nonneg_right hδ (abs_nonneg u)

/-- The two conjugate transforms differ only through transverse depth. -/
theorem norm_square_conjugate_difference_le {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) (ρ : ℂ) :
    ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 ≤
      4 * squareDepthEnergy (ρ.re - 1 / 2) a * ∫ u, ‖f u‖ ^ 2 := by
  let δ : ℝ := ρ.re - 1 / 2
  have hg : gammaOf ρ = (ρ.im : ℂ) - I * (δ : ℂ) := by
    apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, δ] <;> ring
  have hgc : conj (gammaOf ρ) = (ρ.im : ℂ) + I * (δ : ℂ) := by
    rw [hg]
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, sub_neg_eq_add]
  rcases lt_trichotomy 0 δ with hδ | hδ | hδ
  · rw [hgc, hg, squareDepthEnergy_eq_pairEnergy hδ ha]
    exact SquareRootThreshold.norm_sub_sq_le_pairEnergy hδ ha ρ.im hf hfs
  · have hz : ρ.re - 1 / 2 = 0 := hδ.symm
    rw [hgc, hg]
    simp only [← hδ, Complex.ofReal_zero, mul_zero, sub_zero, add_zero,
      sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), hz, squareDepthEnergy_zero,
      zero_mul, le_refl]
  · have hδ' : 0 < -δ := neg_pos.mpr hδ
    have hE : squareDepthEnergy (ρ.re - 1 / 2) a = squareDepthEnergy (-δ) a := by
      unfold squareDepthEnergy
      congr 1
      funext u
      simp only [neg_mul, Real.sinh_neg, neg_sq, δ]
    have hneg := SquareRootThreshold.norm_sub_sq_le_pairEnergy hδ' ha ρ.im hf hfs
    rw [← squareDepthEnergy_eq_pairEnergy hδ' ha] at hneg
    rw [hgc, hg, hE]
    simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hneg
    simpa only [norm_sub_rev] using hneg

/-- Each actual spectral square has a negative part controlled by its
transverse depth and the packet's squared norm. -/
theorem re_square_ge_depth_energy (Z : ZeroConfig) {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) (ρ : ℂ) :
    -(Z.mult ρ : ℝ) * squareDepthEnergy (ρ.re - 1 / 2) a * (∫ u, ‖f u‖ ^ 2) ≤
      (Z.Wsummand f f ρ).re := by
  have h1 := norm_square_conjugate_difference_le ha hf hfs ρ
  have h2 := WindowVisibilityLaw.neg_quarter_norm_sub_sq_le_re_Wsummand Z f ρ
  have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (Z.mult ρ) : (0 : ℝ) ≤ Z.mult ρ)
  nlinarith only [h2, h3]

/-- The classical repulsion margin, on the logarithmic conductor scale. -/
def twistedRepulsionMargin (C : ℝ) (q : ℕ) (β γ : ℝ) : ℝ :=
  Real.log (1 / (C * (1 - β) * Real.log ((q : ℝ) * (|γ| + 3)))) /
    (C * Real.log ((q : ℝ) * (|γ| + 3)))

/-- Maximum remaining transverse depth after the exceptional square's
repulsion. A margin of one half leaves only central squares. -/
def twistedRepulsionDepth (C : ℝ) (q : ℕ) (β γ : ℝ) : ℝ :=
  max 0 (1 / 2 - twistedRepulsionMargin C q β γ)

/-- The conductor-dependent margin controls every remaining square of the
actual twisted zero sum. The exceptional zero and its reflection are the
only excluded points; no spectral repulsion estimate is assumed. -/
theorem exists_twisted_square_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (hq : 1 < q)
      (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (_hquad : χ.IsQuadratic)
      (β : ℝ), 0 < β → χ.LFunction (β : ℂ) = 0 →
      ∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
        ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) →
        twistedRepulsionMargin C q β ρ.im ≤ 1 / 2 - |ρ.re - 1 / 2| ∧
        ∀ (a : ℝ), 0 ≤ a → ∀ (f : ℝ → ℂ), Continuous f →
          tsupport f ⊆ Icc (-a) a →
          -((_root_.RHTower.dirichletZeros hq hprim).mult ρ : ℝ) *
              squareDepthEnergy (twistedRepulsionDepth C q β ρ.im) a * (∫ u, ‖f u‖ ^ 2) ≤
            ((_root_.RHTower.dirichletZeros hq hprim).Wsummand f f ρ).re := by
  obtain ⟨C, hC, hrep⟩ := ExceptionalLayerTheory.exists_deuring_heilbronn_repulsion
  refine ⟨C, hC, ?_⟩
  intro q inst hq χ hprim hquad β hβ hβzero ρ hρ hne hne'
  have hχ : χ ≠ 1 := _root_.RHTower.ne_one_of_isPrimitive hq hprim
  have hz : Zeta23.ThmE.IsNontrivialZeroL χ ρ := by
    rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hρ
  have hmargin : twistedRepulsionMargin C q β ρ.im ≤ 1 / 2 - |ρ.re - 1 / 2| := by
    rcases le_total (1 / 2) ρ.re with hr | hr
    · have hρ1 : ρ ≠ 1 := by
        intro he
        have hh := hz.2.2
        rw [he, Complex.one_re] at hh
        exact (lt_irrefl _ hh)
      have hh := hrep χ hχ hprim hquad β ρ hβ hβzero hr hρ1 (Or.inr hz.1) hne
      change twistedRepulsionMargin C q β ρ.im ≤ 1 - ρ.re at hh
      rw [abs_of_nonneg (sub_nonneg.mpr hr)]
      linarith only [hh]
    · have hρ' := (_root_.RHTower.dirichletZeros hq hprim).reflect_mem ρ hρ
      have hz' : Zeta23.ThmE.IsNontrivialZeroL χ (reflect ρ) := by
        rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hρ'
      have hre : (reflect ρ).re = 1 - ρ.re := by
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      have him : (reflect ρ).im = ρ.im := by
        simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add]
      have hρ1 : reflect ρ ≠ 1 := by
        intro he
        have hh := hz'.2.2
        rw [he, Complex.one_re] at hh
        exact (lt_irrefl _ hh)
      have hneq : reflect ρ ≠ (β : ℂ) := by
        intro he
        apply hne'
        have hh := congrArg reflect he
        have hinv : reflect (reflect ρ) = ρ := by
          apply Complex.ext <;> simp [reflect]
        rwa [hinv] at hh
      have hh := hrep χ hχ hprim hquad β (reflect ρ) hβ hβzero
        (by rw [hre]; linarith only [hr]) hρ1 (Or.inr hz'.1) hneq
      change twistedRepulsionMargin C q β (reflect ρ).im ≤ 1 - (reflect ρ).re at hh
      rw [hre, him] at hh
      rw [abs_of_nonpos (sub_nonpos.mpr hr)]
      linarith only [hh]
  have hdepth : |ρ.re - 1 / 2| ≤ twistedRepulsionDepth C q β ρ.im :=
    (show |ρ.re - 1 / 2| ≤ 1 / 2 - twistedRepulsionMargin C q β ρ.im by
      linarith only [hmargin]).trans (le_max_right _ _)
  refine ⟨hmargin, ?_⟩
  intro a ha f hf hfs
  have hD : 0 ≤ twistedRepulsionDepth C q β ρ.im := le_max_left _ _
  have henergy := squareDepthEnergy_mono (a := a)
    (show |ρ.re - 1 / 2| ≤ |twistedRepulsionDepth C q β ρ.im| by
      rwa [abs_of_nonneg hD])
  have hmult := mul_le_mul_of_nonneg_left henergy
    (Nat.cast_nonneg ((_root_.RHTower.dirichletZeros hq hprim).mult ρ) : (0 : ℝ) ≤ _)
  have hmass := mul_le_mul_of_nonneg_right hmult
    (show 0 ≤ ∫ u : ℝ, ‖f u‖ ^ 2 from integral_nonneg fun u => sq_nonneg ‖f u‖)
  have hbase := re_square_ge_depth_energy (_root_.RHTower.dirichletZeros hq hprim) ha hf hfs ρ
  linarith only [hmass, hbase]

/-- A positive logarithmic margin strictly improves the trivial strip depth. -/
theorem twistedRepulsionDepth_lt_half {C β γ : ℝ} {q : ℕ}
    (hm : 0 < twistedRepulsionMargin C q β γ) :
    twistedRepulsionDepth C q β γ < 1 / 2 := by
  exact max_lt (by norm_num) (by linarith only [hm])

/-- On the actual twisted comb, the explicit-formula limit and the
Deuring–Heilbronn margin hold with one absolute constant. Every remaining
spectral square carries the stated hyperbolic energy bound. -/
theorem exists_twistedComb_square_margin :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (hq : 1 < q)
      (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (_hquad : χ.IsQuadratic)
      (β : ℝ), 0 < β → χ.LFunction (β : ℂ) = 0 →
      ∀ (f : ℝ → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ K : ℕ, 1 ≤ K → (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
        Tendsto (fun N : ℕ => twistedForm χ f (3 * K) N +
          2 * weightedContact (twistWeight χ) f (3 * K) N) atTop
          (𝓝 (-twistedZeroSum hq hprim f)) ∧
        ∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
          ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) →
          twistedRepulsionMargin C q β ρ.im ≤ 1 / 2 - |ρ.re - 1 / 2| ∧
          ∀ (a : ℝ), 0 ≤ a → tsupport (fun u => (f u : ℂ)) ⊆ Icc (-a) a →
            -((_root_.RHTower.dirichletZeros hq hprim).mult ρ : ℝ) *
                squareDepthEnergy (twistedRepulsionDepth C q β ρ.im) a * (∫ u, f u ^ 2) ≤
              ((_root_.RHTower.dirichletZeros hq hprim).Wsummand
                (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re := by
  obtain ⟨C, hC, hrep⟩ := exists_twisted_square_repulsion
  refine ⟨C, hC, ?_⟩
  intro q inst hq χ hprim hquad β hβ hβzero f hf hfc K hK hsupp
  refine ⟨tendsto_twistedForm_add_twistedContact hq hprim hf hfc hK hsupp, ?_⟩
  intro ρ hρ hne hne'
  obtain ⟨hmargin, hbound⟩ := hrep q hq χ hprim hquad β hβ hβzero ρ hρ hne hne'
  refine ⟨hmargin, ?_⟩
  intro a ha hfs
  have hh := hbound a ha (fun u => (f u : ℂ)) (Complex.continuous_ofReal.comp hf.continuous) hfs
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.exists_twisted_square_repulsion
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.exists_twistedComb_square_margin
