import GaloisForLFunctions.RHTower.ResidueJetSpectralSuspension
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compact-open convergence of residue-jet determinant characters

This module upgrades pointwise residue-jet convergence to genuine compact-open convergence.
Residue polynomials, exponential characters, and determinant characters are bundled as continuous
maps on the complex plane with compact-open topology.  Coordinatewise convergence of finite jet
and compact-open convergence of divisor-carrying core imply locally uniform convergence of full
determinant character.

Operator-specific construction and continuity of regularized Fredholm determinant remain
separate analytic infrastructure.
-/

open scoped BigOperators
open Finset Filter Topology

noncomputable section

namespace RHTower

/-- Continuous monomial on complex spectral plane. -/
def residueJetMonomialMap (k : ℕ) : C(ℂ, ℂ) :=
  ⟨fun z => z ^ k, continuous_id.pow k⟩

/-- Corrected residue-jet polynomial bundled in compact-open function space. -/
def residueJetPolynomialContinuousMap (p : ℕ) (b : ℕ → ℂ) : C(ℂ, ℂ) :=
  ∑ k ∈ Ico 1 p, b k • residueJetMonomialMap k

@[simp]
theorem residueJetPolynomialContinuousMap_apply (p : ℕ) (b : ℕ → ℂ) (z : ℂ) :
    residueJetPolynomialContinuousMap p b z = residueJetPolynomial p b z := by
  simp [residueJetPolynomialContinuousMap, residueJetMonomialMap, residueJetPolynomial]

/-- Complex exponential as continuous self-map. -/
def complexExpContinuousMap : C(ℂ, ℂ) :=
  ⟨Complex.exp, Complex.continuous_exp⟩

/-- Zero-free corrected residue-jet character in compact-open function space. -/
def residueJetCharacterContinuousMap (p : ℕ) (b : ℕ → ℂ) : C(ℂ, ℂ) :=
  complexExpContinuousMap.comp (residueJetPolynomialContinuousMap p b)

@[simp]
theorem residueJetCharacterContinuousMap_apply (p : ℕ) (b : ℕ → ℂ) (z : ℂ) :
    residueJetCharacterContinuousMap p b z = residueJetCharacter p b z := by
  simp [residueJetCharacterContinuousMap, complexExpContinuousMap,
    residueJetCharacter, residueJetPolynomialContinuousMap_apply]

/-- Full determinant character with arbitrary continuous divisor-carrying core. -/
def residueJetDeterminantContinuousMap
    (p : ℕ) (b : ℕ → ℂ) (core : C(ℂ, ℂ)) : C(ℂ, ℂ) :=
  residueJetCharacterContinuousMap p b * core

@[simp]
theorem residueJetDeterminantContinuousMap_apply
    (p : ℕ) (b : ℕ → ℂ) (core : C(ℂ, ℂ)) (z : ℂ) :
    residueJetDeterminantContinuousMap p b core z =
      residueJetDeterminant p b core z := by
  simp [residueJetDeterminantContinuousMap, residueJetDeterminant,
    residueJetCharacterContinuousMap_apply]

/-- Coordinatewise convergence of finite jet is compact-open polynomial convergence. -/
theorem tendsto_residueJetPolynomialContinuousMap
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    (hb : ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k))) :
    Tendsto (fun n => residueJetPolynomialContinuousMap p (b n)) atTop
      (𝓝 (residueJetPolynomialContinuousMap p bLim)) := by
  unfold residueJetPolynomialContinuousMap
  apply tendsto_finsetSum
  intro k hk
  exact (hb k hk).smul tendsto_const_nhds

/-- Exponentiating finite jet preserves compact-open convergence. -/
theorem tendsto_residueJetCharacterContinuousMap
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    (hb : ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k))) :
    Tendsto (fun n => residueJetCharacterContinuousMap p (b n)) atTop
      (𝓝 (residueJetCharacterContinuousMap p bLim)) := by
  exact (ContinuousMap.continuous_postcomp complexExpContinuousMap).continuousAt.tendsto.comp
    (tendsto_residueJetPolynomialContinuousMap hb)

/-- Forward compact-open universal law for convergent corrected jet and core. -/
theorem tendsto_residueJetDeterminantContinuousMap
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    {core : ℕ → C(ℂ, ℂ)} {coreLim : C(ℂ, ℂ)}
    (hb : ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)))
    (hcore : Tendsto core atTop (𝓝 coreLim)) :
    Tendsto (fun n => residueJetDeterminantContinuousMap p (b n) (core n)) atTop
      (𝓝 (residueJetDeterminantContinuousMap p bLim coreLim)) := by
  exact (tendsto_residueJetCharacterContinuousMap hb).mul hcore

/-- Equivalent unbundled statement: determinant characters converge locally uniformly. -/
theorem tendstoLocallyUniformly_residueJetDeterminant
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    {core : ℕ → C(ℂ, ℂ)} {coreLim : C(ℂ, ℂ)}
    (hb : ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)))
    (hcore : Tendsto core atTop (𝓝 coreLim)) :
    TendstoLocallyUniformly
      (fun n z => residueJetDeterminant p (b n) (core n) z)
      (residueJetDeterminant p bLim coreLim) atTop := by
  have hmap := tendsto_residueJetDeterminantContinuousMap hb hcore
  have hloc :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hmap
  have hlim :
      (residueJetDeterminantContinuousMap p bLim coreLim : ℂ → ℂ) =
        residueJetDeterminant p bLim coreLim := by
    funext z
    exact residueJetDeterminantContinuousMap_apply p bLim coreLim z
  rw [hlim] at hloc
  simpa only [residueJetDeterminantContinuousMap_apply] using hloc

/-- Residue-jet character is entire. -/
theorem residueJetCharacter_differentiable (p : ℕ) (b : ℕ → ℂ) :
    Differentiable ℂ (residueJetCharacter p b) := by
  have hfun :
      residueJetCharacter p b =
        Complex.exp ∘ fun w => (residueJetPolynomialFormal p b).eval w := by
    funext w
    simp [residueJetCharacter, residueJetPolynomialFormal_eval]
  rw [hfun]
  exact Complex.differentiable_exp.comp
    (residueJetPolynomialFormal p b).differentiable

/-- Logarithmic derivative removes exponential ambiguity and exposes formal derivative. -/
theorem residueJetCharacter_logDeriv (p : ℕ) (b : ℕ → ℂ) (z : ℂ) :
    logDeriv (residueJetCharacter p b) z =
      (residueJetPolynomialFormal p b).derivative.eval z := by
  have hfun :
      residueJetCharacter p b =
        Complex.exp ∘ fun w => (residueJetPolynomialFormal p b).eval w := by
    funext w
    simp [residueJetCharacter, residueJetPolynomialFormal_eval]
  rw [hfun, logDeriv_comp Complex.differentiableAt_exp
    (residueJetPolynomialFormal p b).differentiableAt]
  rw [Complex.logDeriv_exp]
  simp

/-- Iterated derivative at zero recovers factorial-scaled formal coefficient. -/
theorem residueJetFormal_iterateDerivative_eval_zero
    (p : ℕ) (b : ℕ → ℂ) (k : ℕ) :
    ((Polynomial.derivative^[k]) (residueJetPolynomialFormal p b)).eval 0 =
      (k.factorial : ℂ) * (residueJetPolynomialFormal p b).coeff k := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

theorem residueJetFormal_iterate_derivative_succ
    (P : Polynomial ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (Polynomial.derivative^[k - 1]) P.derivative =
      (Polynomial.derivative^[k]) P := by
  calc
    (Polynomial.derivative^[k - 1]) P.derivative =
        (Polynomial.derivative^[(k - 1).succ]) P :=
      (Function.iterate_succ_apply (f := Polynomial.derivative) (k - 1) P).symm
    _ = (Polynomial.derivative^[k]) P := by
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hk]

/--
Converse compact-open law for residue-jet characters.  Locally uniform convergence of zero-free
characters forces convergence of every corrected residue coordinate; no coefficient can hide
behind exponential periodicity.
-/
theorem tendsto_residueJetCoordinate_of_tendstoLocallyUniformlyOn_character
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : 0 ∈ U)
    (hchar : TendstoLocallyUniformlyOn
      (fun n z => residueJetCharacter p (b n) z)
      (residueJetCharacter p bLim) atTop U) :
    ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)) := by
  have hderivOn := hchar.deriv
    (Eventually.of_forall fun n =>
      (residueJetCharacter_differentiable p (b n)).differentiableOn)
    hU
  have hlogOn :
      TendstoLocallyUniformlyOn
        (fun n z => logDeriv (residueJetCharacter p (b n)) z)
        (logDeriv (residueJetCharacter p bLim)) atTop U := by
    have hdiv := hderivOn.div₀ hchar
      (residueJetCharacter_differentiable p bLim).deriv.continuous.continuousOn
      (residueJetCharacter_differentiable p bLim).continuous.continuousOn
      (fun z _ => Complex.exp_ne_zero _)
    exact (hdiv.congr (fun n z _ => rfl)).congr_right (fun z _ => rfl)
  have hpolyOn :
      TendstoLocallyUniformlyOn
        (fun n z => (residueJetPolynomialFormal p (b n)).derivative.eval z)
        (fun z => (residueJetPolynomialFormal p bLim).derivative.eval z)
        atTop U := by
    apply (hlogOn.congr fun n z _ => residueJetCharacter_logDeriv p (b n) z).congr_right
    intro z _
    exact residueJetCharacter_logDeriv p bLim z
  intro k hk
  have hiter :
      TendstoLocallyUniformlyOn
        (fun n z =>
          ((Polynomial.derivative^[k - 1])
            (residueJetPolynomialFormal p (b n)).derivative).eval z)
        (fun z =>
          ((Polynomial.derivative^[k - 1])
            (residueJetPolynomialFormal p bLim).derivative).eval z)
        atTop U := by
    induction k - 1 with
    | zero =>
        simpa using hpolyOn
    | succ m ih =>
        have hd := ih.deriv
          (Eventually.of_forall fun n =>
            (((Polynomial.derivative^[m])
              (residueJetPolynomialFormal p (b n)).derivative).differentiableOn))
          hU
        have hd' := hd.congr (fun n z _ => by
          change deriv
            (fun x => ((Polynomial.derivative^[m])
              (residueJetPolynomialFormal p (b n)).derivative).eval x) z =
            ((Polynomial.derivative^[m + 1])
              (residueJetPolynomialFormal p (b n)).derivative).eval z
          rw [Polynomial.deriv, Function.iterate_succ_apply'])
        exact hd'.congr_right (fun z _ => by
          change deriv
            (fun x => ((Polynomial.derivative^[m])
              (residueJetPolynomialFormal p bLim).derivative).eval x) z =
            ((Polynomial.derivative^[m + 1])
              (residueJetPolynomialFormal p bLim).derivative).eval z
          rw [Polynomial.deriv, Function.iterate_succ_apply'])
  have hat0 := hiter.tendsto_at h0
  have hkpos : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hscaled :
      Tendsto
        (fun n => (k.factorial : ℂ) * b n k)
        atTop (𝓝 ((k.factorial : ℂ) * bLim k)) := by
    simpa only [residueJetFormal_iterate_derivative_succ _ hkpos,
      residueJetFormal_iterateDerivative_eval_zero,
      residueJetPolynomialFormal_coeff hkpos (Finset.mem_Ico.mp hk).2] using hat0
  have hkfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hinv :
      Tendsto (fun _ : ℕ => (k.factorial : ℂ)⁻¹) atTop
        (𝓝 (k.factorial : ℂ)⁻¹) :=
    tendsto_const_nhds
  simpa [hkfac] using hinv.mul hscaled

/-- Global compact-open converse as specialization of neighborhood theorem. -/
theorem tendsto_residueJetCoordinate_of_tendstoLocallyUniformly_character
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    (hchar : TendstoLocallyUniformly
      (fun n z => residueJetCharacter p (b n) z)
      (residueJetCharacter p bLim) atTop) :
    ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)) :=
  tendsto_residueJetCoordinate_of_tendstoLocallyUniformlyOn_character
    isOpen_univ (Set.mem_univ 0) hchar.tendstoLocallyUniformlyOn

/--
Converse determinant law after cancellation of common zero-free local core.  This is exact
formal counterpart of choosing small spectral disk free of regularized Fredholm zeros.
-/
theorem tendsto_residueJetCoordinate_of_tendstoLocallyUniformlyOn_determinant
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ} {U : Set ℂ}
    {core : ℕ → C(ℂ, ℂ)} {coreLim : C(ℂ, ℂ)}
    (hU : IsOpen U) (h0 : 0 ∈ U)
    (hdet : TendstoLocallyUniformlyOn
      (fun n z => residueJetDeterminant p (b n) (core n) z)
      (residueJetDeterminant p bLim coreLim) atTop U)
    (hcore : TendstoLocallyUniformlyOn
      (fun n z => core n z) coreLim atTop U)
    (hcoreLim_ne : ∀ z ∈ U, coreLim z ≠ 0)
    (hcore_ne : ∀ᶠ n in atTop, ∀ z ∈ U, core n z ≠ 0) :
    ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)) := by
  have hdetCont : ContinuousOn (residueJetDeterminant p bLim coreLim) U := by
    have heq :
        residueJetDeterminant p bLim coreLim =
          (residueJetDeterminantContinuousMap p bLim coreLim : ℂ → ℂ) := by
      funext z
      exact (residueJetDeterminantContinuousMap_apply p bLim coreLim z).symm
    rw [heq]
    exact (residueJetDeterminantContinuousMap p bLim coreLim).continuous.continuousOn
  have hquot := hdet.div₀ hcore
    hdetCont coreLim.continuous.continuousOn hcoreLim_ne
  have hchar :
      TendstoLocallyUniformlyOn
        (fun n z => residueJetCharacter p (b n) z)
        (residueJetCharacter p bLim) atTop U := by
    have hleft :
        TendstoLocallyUniformlyOn
          (fun n z => residueJetCharacter p (b n) z)
          (residueJetDeterminant p bLim coreLim / coreLim) atTop U :=
      hquot.congr_inseparable (hcore_ne.mono fun n hn z hz => by
        apply Inseparable.of_eq
        simp [residueJetDeterminant, hn z hz])
    apply hleft.congr_right
    intro z hz
    simp [residueJetDeterminant, hcoreLim_ne z hz]
  exact tendsto_residueJetCoordinate_of_tendstoLocallyUniformlyOn_character hU h0 hchar

/--
Exact compact-open convergence criterion for factorized determinant characters.  Once common
core converges and is eventually zero-free near origin, full determinant convergence is
equivalent to convergence of every corrected residue-jet coordinate.
-/
theorem residueJetDeterminantContinuousMap_tendsto_iff
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ} {U : Set ℂ}
    {core : ℕ → C(ℂ, ℂ)} {coreLim : C(ℂ, ℂ)}
    (hU : IsOpen U) (h0 : 0 ∈ U)
    (hcore : Tendsto core atTop (𝓝 coreLim))
    (hcoreLim_ne : ∀ z ∈ U, coreLim z ≠ 0)
    (hcore_ne : ∀ᶠ n in atTop, ∀ z ∈ U, core n z ≠ 0) :
    Tendsto (fun n => residueJetDeterminantContinuousMap p (b n) (core n)) atTop
        (𝓝 (residueJetDeterminantContinuousMap p bLim coreLim)) ↔
      ∀ k ∈ Ico 1 p, Tendsto (fun n => b n k) atTop (𝓝 (bLim k)) := by
  constructor
  · intro hdet
    have hdetLoc :=
      ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hdet
    have hcoreLoc :=
      ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hcore
    have hdetOn :
        TendstoLocallyUniformlyOn
          (fun n z => residueJetDeterminant p (b n) (core n) z)
          (residueJetDeterminant p bLim coreLim) atTop U := by
      have h := hdetLoc.tendstoLocallyUniformlyOn (s := U)
      have hlim :
          (residueJetDeterminantContinuousMap p bLim coreLim : ℂ → ℂ) =
            residueJetDeterminant p bLim coreLim := by
        funext z
        exact residueJetDeterminantContinuousMap_apply p bLim coreLim z
      rw [hlim] at h
      simpa only [residueJetDeterminantContinuousMap_apply] using h
    have hcoreOn :
        TendstoLocallyUniformlyOn
          (fun n z => core n z) coreLim atTop U :=
      hcoreLoc.tendstoLocallyUniformlyOn
    exact tendsto_residueJetCoordinate_of_tendstoLocallyUniformlyOn_determinant
      hU h0 hdetOn hcoreOn hcoreLim_ne hcore_ne
  · intro hb
    exact tendsto_residueJetDeterminantContinuousMap hb hcore

end RHTower
