import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherGalilean
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanClosure
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaMaNLS
import Mathlib.Tactic

/-!
# Certified moving breather solutions

The velocity substitution after paper equation (36) is upgraded from a field identity to a closed
NLS certificate.  The explicit Akhmediev and Ma jets obey the missing chain rule along every affine
transport line, so the corpus's Galilean closure theorem applies without theorem-side hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

theorem hasDerivAt_linearPhase_transport (ω k c t x : ℝ) :
    HasDerivAt (fun s => linearPhase ω k s (x - c * s))
      (linearPhase ω k t (x - c * t) * (Complex.I * ((ω - c * k : ℝ) : ℂ))) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
  have ht := hasDerivAt_staggerPhase (-ω) t
  have hx := (hasDerivAt_staggerPhase (-k) (x - c * t)).scomp t hinner
  have h := ht.mul hx
  apply h.congr_deriv
  simp only [linearPhase, Function.comp_apply, Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_akhmedievDenominator_transport
    (φ : BreatherAngle) (c t x : ℝ) :
    HasDerivAt (fun s => akhmedievDenominator φ (x - c * s) s)
      (akhmedievDenominatorT φ t - c * akhmedievDenominatorX φ (x - c * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
  have hx := (hasDerivAt_akhmedievDenominator_space φ (x - c * t) t).scomp t hinner
  have ht := hasDerivAt_akhmedievDenominator_time φ x t
  have h := hx.add ht |>.sub_const (akhmedievDenominator φ x t)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.add_apply, Function.comp_apply, akhmedievDenominator]
    ring
  · simp only [smul_eq_mul]
    ring

theorem hasDerivAt_akhmedievNumerator_transport
    (φ : BreatherAngle) (c t x : ℝ) :
    HasDerivAt (fun s => akhmedievNumerator φ (x - c * s) s)
      (akhmedievNumeratorT φ t - (c : ℂ) * akhmedievNumeratorX φ (x - c * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
  have hx := (hasDerivAt_akhmedievNumerator_space φ (x - c * t) t).scomp t hinner
  have ht := hasDerivAt_akhmedievNumerator_time φ x t
  have h := hx.add ht |>.sub_const (akhmedievNumerator φ x t)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.add_apply, Function.comp_apply, akhmedievNumerator]
    push_cast
    ring
  · simp only [Complex.real_smul]
    push_cast
    ring

theorem hasDerivAt_akhmedievCore_transport (φ : BreatherAngle) (c t x : ℝ) :
    HasDerivAt (fun s => akhmedievCore φ (x - c * s) s)
      (akhmedievCoreT φ (x - c * t) t - (c : ℂ) * akhmedievCoreX φ (x - c * t) t) t := by
  have hn := hasDerivAt_akhmedievNumerator_transport φ c t x
  have hd := (hasDerivAt_akhmedievDenominator_transport φ c t x).ofReal_comp
  have h := hn.div hd (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (akhmedievDenominator_pos φ (x - c * t) t))) |>.neg
  apply h.congr_deriv
  simp only [akhmedievCoreT, akhmedievCoreX]
  field_simp [Complex.ofReal_ne_zero.mpr
    (ne_of_gt (akhmedievDenominator_pos φ (x - c * t) t))]
  push_cast
  ring

theorem hasDerivAt_akhmedievBreather_transport (φ : BreatherAngle) (c t x : ℝ) :
    HasDerivAt (fun s => akhmedievBreather φ (x - c * s) s)
      ((akhmedievBreatherJet φ).ut t (x - c * t) -
        (c : ℂ) * (akhmedievBreatherJet φ).ux t (x - c * t)) t := by
  have hc := hasDerivAt_akhmedievCore_transport φ c t x
  have hp := hasDerivAt_linearPhase_transport 1 0 c t x
  have h := hc.mul hp |>.div_const (Real.sqrt 2 : ℂ)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.mul_apply, akhmedievBreather, akhmedievCore]
  · simp only [akhmedievBreatherJet]
    norm_num
    ring

noncomputable def akhmedievTransportJet (φ : BreatherAngle) : TransportCompatibleJet2 where
  toComplexEvolutionJet2 := akhmedievBreatherJet φ
  hasDerivAt_transport := hasDerivAt_akhmedievBreather_transport φ

abbrev TransportCompatibleFocusingSolution :=
  {J : TransportCompatibleJet2 // SolvesFocusingNLS J.toComplexEvolutionJet2}

/-- Galilean closure for the coefficient-`2` focusing normalization used by both breathers. -/
noncomputable def galileanFocusingSolution (v : ℝ)
    (S : TransportCompatibleFocusingSolution) : FocusingSolutionJet :=
  ⟨galileanJet 1 v S, by
    intro t x
    have h := S.property t (x - 2 * v * t)
    simp only [galileanJet]
    rw [norm_mul, norm_linearPhase, mul_one]
    push_cast at h ⊢
    calc
      _ = linearPhase (-v ^ (2 : ℕ)) v t x *
          (Complex.I * S.val.ut t (x - 2 * v * t) +
            S.val.uxx t (x - 2 * v * t) +
            (2 : ℂ) * (‖S.val.u t (x - 2 * v * t)‖ : ℂ) ^ (2 : ℕ) *
              S.val.u t (x - 2 * v * t)) := by ring_nf
      _ = 0 := by
        apply mul_eq_zero_of_right
        exact h⟩

theorem galileanFocusingSolution_solves (v : ℝ)
    (S : TransportCompatibleFocusingSolution) :
    SolvesFocusingNLS (galileanFocusingSolution v S).val :=
  (galileanFocusingSolution v S).property

theorem galileanFocusingSolution_field (v : ℝ)
    (S : TransportCompatibleFocusingSolution) (t x : ℝ) :
    (galileanFocusingSolution v S).val.u t x = galileanField 1 v S.val.u t x := by
  rfl

noncomputable def akhmedievTransportSolution (φ : BreatherAngle) :
    TransportCompatibleFocusingSolution :=
  ⟨akhmedievTransportJet φ, by
    simpa only [akhmedievTransportJet] using akhmedievBreather_solves φ⟩

noncomputable def movingAkhmedievSolution (u : ℝ) (φ : BreatherAngle) :
    FocusingSolutionJet :=
  galileanFocusingSolution (u / 2) (akhmedievTransportSolution φ)

theorem movingAkhmedievSolution_field (u : ℝ) (φ : BreatherAngle) (τ ξ : ℝ) :
    (movingAkhmedievSolution u φ).val.u τ ξ = movingAkhmedievBreather u φ ξ τ := by
  rw [movingAkhmedievSolution, galileanFocusingSolution_field,
    movingAkhmedievBreather, dimensionlessGalileanField_eq_galileanField]
  rfl

theorem movingAkhmedievSolution_solves (u : ℝ) (φ : BreatherAngle) :
    SolvesFocusingNLS (movingAkhmedievSolution u φ).val :=
  (movingAkhmedievSolution u φ).property

theorem hasDerivAt_maDenominator_transport (φ : MaAngle) (c t x : ℝ) :
    HasDerivAt (fun s => maDenominator φ (x - c * s) s)
      (maDenominatorT φ t - c * maDenominatorX φ (x - c * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
  have hx := (hasDerivAt_maDenominator_space φ (x - c * t) t).scomp t hinner
  have ht := hasDerivAt_maDenominator_time φ x t
  have h := hx.add ht |>.sub_const (maDenominator φ x t)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.add_apply, Function.comp_apply, maDenominator]
    ring
  · simp only [smul_eq_mul]
    ring

theorem hasDerivAt_maNumerator_transport (φ : MaAngle) (c t x : ℝ) :
    HasDerivAt (fun s => maNumerator φ (x - c * s) s)
      (maNumeratorT φ t - (c : ℂ) * maNumeratorX φ (x - c * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
  have hx := (hasDerivAt_maNumerator_space φ (x - c * t) t).scomp t hinner
  have ht := hasDerivAt_maNumerator_time φ x t
  have h := hx.add ht |>.sub_const (maNumerator φ x t)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.add_apply, Function.comp_apply, maNumerator]
    push_cast
    ring
  · simp only [Complex.real_smul]
    push_cast
    ring

theorem hasDerivAt_maCore_transport (φ : MaAngle) (c t x : ℝ) :
    HasDerivAt (fun s => maCore φ (x - c * s) s)
      (maCoreT φ (x - c * t) t - (c : ℂ) * maCoreX φ (x - c * t) t) t := by
  have hn := hasDerivAt_maNumerator_transport φ c t x
  have hd := (hasDerivAt_maDenominator_transport φ c t x).ofReal_comp
  have h := hn.div hd (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (maDenominator_pos φ (x - c * t) t))) |>.neg
  apply h.congr_deriv
  simp only [maCoreT, maCoreX]
  field_simp [Complex.ofReal_ne_zero.mpr
    (ne_of_gt (maDenominator_pos φ (x - c * t) t))]
  push_cast
  ring

theorem hasDerivAt_maBreather_transport (φ : MaAngle) (c t x : ℝ) :
    HasDerivAt (fun s => maBreather φ (x - c * s) s)
      ((maBreatherJet φ).ut t (x - c * t) -
        (c : ℂ) * (maBreatherJet φ).ux t (x - c * t)) t := by
  have hc := hasDerivAt_maCore_transport φ c t x
  have hp := hasDerivAt_linearPhase_transport 1 0 c t x
  have h := hc.mul hp |>.div_const (Real.sqrt 2 : ℂ)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with s
    simp only [Pi.mul_apply, maBreather]
  · simp only [maBreatherJet]
    norm_num
    ring

noncomputable def maTransportJet (φ : MaAngle) : TransportCompatibleJet2 where
  toComplexEvolutionJet2 := maBreatherJet φ
  hasDerivAt_transport := hasDerivAt_maBreather_transport φ

noncomputable def maTransportSolution (φ : MaAngle) :
    TransportCompatibleFocusingSolution :=
  ⟨maTransportJet φ, by
    simpa only [maTransportJet] using maBreather_solves φ⟩

noncomputable def movingMaSolution (u : ℝ) (φ : MaAngle) : FocusingSolutionJet :=
  galileanFocusingSolution (u / 2) (maTransportSolution φ)

theorem movingMaSolution_field (u : ℝ) (φ : MaAngle) (τ ξ : ℝ) :
    (movingMaSolution u φ).val.u τ ξ = movingMaBreather u φ ξ τ := by
  rw [movingMaSolution, galileanFocusingSolution_field,
    movingMaBreather, dimensionlessGalileanField_eq_galileanField]
  rfl

theorem movingMaSolution_solves (u : ℝ) (φ : MaAngle) :
    SolvesFocusingNLS (movingMaSolution u φ).val :=
  (movingMaSolution u φ).property

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
