import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.HTGeometry.SignConstancy

/-!
# Exponential coordinates for the Lévy head

Each exponential mode of the archimedean density reads one positive-real Laplace
value of the profile. The first mode cancels the positive half-charge exactly.
For an actual critical state, zero-freeness fixes the sign of every sample. The
remaining resolvent sum therefore has strictly signed real part on the left
half-plane, constraining the balance of the state, prime heads and negative charge.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Integrating one exponential mode of the head gives its Laplace resolvent. -/
theorem integral_exponential_mul_levyHead {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {r : ℝ} (hr : 0 < r)
    {p : ℂ} (hp : p.re < r) :
    (∫ x in Ioi (0 : ℝ), cexp (((p - r) : ℂ) * x) * levyHead F p x) =
      negativeHalfLineLaplace (cx F) r / ((r : ℂ) - p) := by
  let f : ℝ × ℝ → ℂ := fun q =>
    if -q.1 < q.2 then cexp ((p - r) * q.1) * (cexp (p * q.2) * (F q.2 : ℂ)) else 0
  let σ : ℝ := max p.re 0
  have hσ : σ < r := max_lt hp hr
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_lt measurable_fst.neg measurable_snd)
      ((by fun_prop : Measurable fun q : ℝ × ℝ => cexp ((p - r) * q.1)).mul
        ((by fun_prop : Measurable fun q : ℝ × ℝ => cexp (p * q.2)).mul
          (Complex.measurable_ofReal.comp (hF.meas.comp measurable_snd)))) measurable_const
  have hdom := (integrableOn_exp_mul_Ioi (by linarith : σ - r < 0) 0).mul_prod hF.integrable.abs
  have hi : Integrable f ((volume.restrict (Ioi 0)).prod volume) := by
    refine hdom.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    dsimp only [f]
    split_ifs with hq
    · rcases lt_or_ge q.2 0 with hu | hu
      · rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, norm_cexp_mul_ofReal,
          Complex.norm_real, Real.norm_eq_abs, ← mul_assoc, ← Real.exp_add]
        simp only [Complex.sub_re, Complex.ofReal_re]
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        have h1 : 0 ≤ (σ - p.re) * (q.1 + q.2) :=
          mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (by linarith)
        have h2 : σ * q.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) hu.le
        nlinarith only [h1,h2]
      · simp only [hF.support q.2 hu, Complex.ofReal_zero, mul_zero, norm_zero, abs_zero, le_refl]
    · simp only [norm_zero]
      positivity
  have hrow (x : ℝ) : (∫ u, f (x,u)) = cexp ((p - r) * x) * levyHead F p x := by
    change (∫ u, (Ioi (-x)).indicator
      (fun u => cexp ((p - r) * x) * (cexp (p * u) * (F u : ℂ))) u) = _
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]
    rw [levyHead, integral_Ici_eq_integral_Ioi]
  have hcol (u : ℝ) : (∫ x in Ioi (0 : ℝ), f (x,u)) =
      cexp ((r : ℂ) * u) * (F u : ℂ) / ((r : ℂ) - p) := by
    rcases lt_or_ge u 0 with hu | hu
    · have hf : (fun x => f (x,u)) = (Ioi (-u)).indicator
          (fun x => cexp ((p - r) * x) * (cexp (p * u) * (F u : ℂ))) := by
        funext x
        simp only [f, Set.indicator, mem_Ioi]
        congr 1
        exact propext (by constructor <;> intro h <;> linarith)
      rw [hf, setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ -u)), integral_mul_const,
        integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hp)]
      have he : cexp ((p - r) * ((-u : ℝ) : ℂ)) * cexp (p * u) = cexp ((r : ℂ) * u) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← he]
      have hn : p - (r : ℂ) = -((r : ℂ) - p) := by ring
      rw [hn, div_neg]
      ring
    · simp [f, hF.support u hu]
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∫ u, f (x,u) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ => (hrow x).symm
    _ = ∫ u, ∫ x in Ioi (0 : ℝ), f (x,u) := integral_integral_swap hi
    _ = ∫ u : ℝ, cexp ((r : ℂ) * u) * (F u : ℂ) / ((r : ℂ) - p) :=
      integral_congr_ae (Eventually.of_forall hcol)
    _ = _ := by rw [integral_div]; rfl

/-- The Lévy head is the absolutely convergent resolvent sum of the positive-real
Laplace samples at the archimedean frequencies `2k+1/2`. -/
theorem hasSum_levyHead_resolvents {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : p.re < 1/2) :
    HasSum (fun k : ℕ =>
      negativeHalfLineLaplace (cx F) (2*k+1/2) / ((2*k+1/2 : ℂ)-p))
      (levyHeadTerm F p) := by
  let q : ℝ → ℂ := fun x => cexp (p*x) * levyHead F p x
  let f : ℕ → ℝ → ℂ := fun k x => (Real.exp (-(2*k+1/2)*x) : ℂ) * q x
  let b : ℕ → ℝ → ℝ := fun k x => Real.exp (-(2*k+1/2)*x) * ‖q x‖
  have hq : StronglyMeasurable q :=
    (by fun_prop : Continuous fun x : ℝ => cexp (p*x)).stronglyMeasurable.mul
      (stronglyMeasurable_levyHead hF.meas p)
  have hbs (x : ℝ) (hx : 0<x) : HasSum (fun k => b k x) (archLevyDensity x * ‖q x‖) :=
    (RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity hx).mul_right _
  have hfs (x : ℝ) (hx : 0<x) : HasSum (fun k => f k x) ((archLevyDensity x : ℂ) * q x) := by
    exact (Complex.ofRealCLM.hasSum (RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity hx)).mul_right _
  have hnorm (x : ℝ) (hx : 0<x) :
      ‖(archLevyDensity x : ℂ) * q x‖ = archLevyDensity x * ‖q x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLevyDensity_pos hx).le]
  obtain ⟨g,hg,hgb⟩ := exists_levyHeadTerm_dominator hF
    (σ := max p.re 0) (le_max_right _ _) (max_lt hp (by norm_num))
  have hJ : IntegrableOn (fun x => (archLevyDensity x : ℂ)*q x) (Ioi 0) := by
    refine hg.mono'
      ((Complex.measurable_ofReal.comp measurable_archLevyDensity').stronglyMeasurable.mul hq).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => hgb x hx p (le_max_left _ _))
  have hs : HasSum (fun k => ∫ x in Ioi (0 : ℝ), f k x) (levyHeadTerm F p) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence b
    · intro k
      exact ((by fun_prop : Continuous fun x : ℝ => (Real.exp (-(2*k+1/2)*x) : ℂ)).stronglyMeasurable.mul hq).aestronglyMeasurable
    · intro k
      exact Eventually.of_forall fun x => by
        dsimp only [f,b]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun x hx => (hbs x hx).summable)
    · refine hJ.norm.congr ?_
      exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun x hx => (hnorm x hx).trans (hbs x hx).tsum_eq.symm)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hfs)
  refine hs.congr_fun fun k => ?_
  have hr : (0 : ℝ) < 2*k+1/2 := by positivity
  have hpk : p.re < 2*(k : ℝ)+1/2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hi := integral_exponential_mul_levyHead hF hr hpk
  have he : (fun x => f k x) =
      (fun x : ℝ => cexp ((p - (2*(k : ℝ)+1/2)) * x) * levyHead F p x) := by
    funext x
    dsimp only [f,q]
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  push_cast at hi ⊢
  exact hi.symm

theorem levyHeadTerm_eq_resolvents {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : p.re < 1/2) :
    levyHeadTerm F p = ∑' k : ℕ,
      negativeHalfLineLaplace (cx F) (2*k+1/2) / ((2*k+1/2 : ℂ)-p) :=
  (hasSum_levyHead_resolvents hF hp).tsum_eq.symm

/-- Removing the first exponential mode removes exactly the positive half-charge. -/
theorem leftRemainder_eq_resolvents {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hp : p.re < -(1/2)) :
    leftRemainder F p =
      (∑' k : ℕ, negativeHalfLineLaplace (cx F) (2*(k+1)+1/2) /
        ((2*(k+1)+1/2 : ℂ)-p)) + primeHead F p +
          negativeHalfLineLaplace (cx F) (-(1/2)) / (p+1/2) := by
  have hs := hasSum_levyHead_resolvents hF (by linarith : p.re < 1/2)
  have he := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at he
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, Nat.cast_add, Nat.cast_one] at he
  rw [leftRemainder, ← he]
  have hden : (1/2 : ℂ)-p = -(p-1/2) := by ring
  rw [hden, div_neg]
  ring

/-- Left of the zero strip, the state is its positive-frequency archimedean
resolvents, prime heads and the negative half-charge. -/
theorem stateMeromorphic_eq_resolvents {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : w.re < -(17/2)) :
    stateMeromorphic W₀ F w =
      -((∑' k : ℕ, negativeHalfLineLaplace (cx F) (2*(k+1)+1/2) /
          ((2*(k+1)+1/2 : ℂ)-(w+8))) + primeHead F (w+8) +
          negativeHalfLineLaplace (cx F) (-(1/2)) / ((w+8)+1/2)) /
        criticalAliasCoefficient W₀ := by
  rw [stateMeromorphic_eq_left hw, leftRemainder_eq_resolvents hF (by simp; linarith)]

/-- Samples at or beyond `1/2` have the same sign as the positive half-charge. -/
theorem criticalState_laplace_half_mul_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s : ℝ} (hs : 1/2 ≤ s) :
    0 < (negativeHalfLineLaplace (cx F) (1/2)).re *
      (negativeHalfLineLaplace (cx F) (s : ℂ)).re := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc : ContinuousOn (fun u : ℝ => (negativeHalfLineLaplace (cx F) (u : ℂ)).re)
      (Icc (1/2) s) := by
    intro u hu
    have hdu := differentiableAt_laplace_of_sq hd hd.exponential (w := (u : ℂ))
      (by simp only [Complex.ofReal_re]; linarith [hu.1])
    exact (Complex.continuous_re.continuousAt.comp
      (hdu.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hn : ∀ u ∈ Icc (1/2 : ℝ) s,
      (negativeHalfLineLaplace (cx F) (u : ℂ)).re ≠ 0 := by
    intro u hu
    rw [negativeHalfLineLaplace_ofReal, Complex.ofReal_re]
    exact criticalHalfLineGroundState_laplace_ne_zero hW ht hF (by linarith [hu.1])
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    _root_.HTGeometry.mul_pos_of_ne_zero_on_Icc hs hc hn

/-- Every archimedean mode remaining after charge cancellation has real part with the sign of
`L F(1/2)`, even though the critical profile changes sign on every ray. -/
theorem criticalState_resolvent_tail_half_re_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {x : ℂ} (hx : x.re < 1/2) :
    0 < (negativeHalfLineLaplace (cx F) (1/2)).re *
      (∑' k : ℕ, negativeHalfLineLaplace (cx F) (2*(k+1)+1/2) /
        ((2*(k+1)+1/2 : ℂ)-x)).re := by
  let r : ℕ → ℝ := fun k => 2*((k : ℝ)+1)+1/2
  let a : ℕ → ℂ := fun k => negativeHalfLineLaplace (cx F) (r k) / ((r k : ℂ)-x)
  let M : ℝ := (negativeHalfLineLaplace (cx F) (1/2)).re
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : Summable a := by
    have h := (summable_nat_add_iff 1).mpr
      (hasSum_levyHead_resolvents hd (p := x) hx).summable
    simpa only [a,r,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] using h
  have hpos (k : ℕ) : 0 < M*(a k).re := by
    have hr : (1/2 : ℝ) ≤ r k := by
      dsimp [r]
      linarith only [Nat.cast_nonneg (α := ℝ) k]
    have hc := criticalState_laplace_half_mul_pos hW ht hF hr
    have hp : 0 < r k-x.re := by linarith
    have hn : (r k : ℂ)-x ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.sub_re,Complex.ofReal_re,Complex.zero_re] at hRe
      linarith
    have he : M*(a k).re =
        (M*(negativeHalfLineLaplace (cx F) (r k)).re)*(r k-x.re) /
          Complex.normSq ((r k : ℂ)-x) := by
      simp only [a,negativeHalfLineLaplace_ofReal,Complex.div_re,
        Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,zero_mul]
      ring
    rw [he]
    exact div_pos (mul_pos hc hp) (Complex.normSq_pos.mpr hn)
  have hb : HasSum (fun k => M*(a k).re) (M*(∑' k,a k).re) :=
    (Complex.reCLM.hasSum ha.hasSum).mul_left M
  have hpositive := hb.summable.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  rw [hb.tsum_eq] at hpositive
  simpa only [a,r,M,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] using hpositive

/-- The actual state's prime heads and negative charge leave a strictly signed
archimedean remainder throughout the left half-plane. -/
theorem criticalState_left_prime_balance_re_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {p : ℂ} (hp : p.re < -(1/2)) :
    0 < (negativeHalfLineLaplace (cx F) (1/2)).re *
      (-((criticalAliasCoefficient W₀ : ℝ) : ℂ) * stateMeromorphic W₀ F (p-8)
        - primeHead F p - negativeHalfLineLaplace (cx F) (-(1/2)) / (p+1/2)).re := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : ((criticalAliasCoefficient W₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  have he : -((criticalAliasCoefficient W₀ : ℝ) : ℂ) * stateMeromorphic W₀ F (p-8)
        - primeHead F p - negativeHalfLineLaplace (cx F) (-(1/2)) / (p+1/2) =
      ∑' k : ℕ, negativeHalfLineLaplace (cx F) (2*(k+1)+1/2) /
        ((2*(k+1)+1/2 : ℂ)-p) := by
    rw [stateMeromorphic_eq_resolvents hd (by simp; linarith)]
    simp only [sub_add_cancel]
    have hcancel (z : ℂ) : -((criticalAliasCoefficient W₀ : ℝ) : ℂ) *
        (-z / criticalAliasCoefficient W₀) = z := by
      field_simp [ha]
    rw [hcancel]
    ring
  rw [he]
  exact criticalState_resolvent_tail_half_re_pos hW ht hF (by linarith)

end GaloisForLFunctions.ExclusionOfTheCriticalState
