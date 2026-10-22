import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiJetPacketSurjectivity
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentCasoratian

/-!
# Simultaneous finite Xi jet packets in literal Meyer cohomology

Every finite set of actual Xi divisor points, with every jet below each
analytic multiplicity, is a simultaneous quotient of the literal all-weight
Meyer cohomology.  This strengthens the one-divisor packet theorem: one Meyer
class realizes an arbitrary confluent packet across all selected divisor
points at once.

The analytic input is an exact confluent Wronskian.  A relation among
logarithmic Mellin jets gives a polynomial-exponential distribution.  Its
complex Wronskian at zero is the transpose of the confluent polynomial jet
matrix, whose determinant is the product of factorials and pairwise divisor
differences.  No dimension count or divisor-indexed source is substituted.

The common kernel is flow-invariant, and the descended flow is the direct
sum of the exact multiplicity-sensitive Jordan packet flows.

This theorem is deliberately finite.  The companion full-packet admission
module proves that arbitrary infinite Xi jet packets are not source-admissible.

All results are unconditional.  No RH, simplicity, positivity, trace,
numerical computation, inverse Mellin theorem, or global synthesis premise is
used.
-/

open Complex Filter Function Set Topology
open scoped Classical
open GaloisForLFunctions

namespace RHTower

noncomputable section

/--
The Wronskian entry for one polynomial-exponential mode is the matching
polynomial derivative evaluation.
-/
theorem iteratedDeriv_cexp_mul_pow_zero
    (rho : ℂ) (n k : ℕ) :
    iteratedDeriv n
        (fun z : ℂ => Complex.exp (rho * z) * z ^ k) 0 =
      ((Polynomial.derivative^[k]) (Polynomial.X ^ n)).eval rho := by
  change
    iteratedDeriv n
        ((fun z : ℂ => Complex.exp (rho * z)) *
          (fun z : ℂ => z ^ k)) 0 = _
  rw [iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_cexp_const_mul, mul_zero,
    Complex.exp_zero, mul_one, iteratedDeriv_fun_pow_zero]
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single (n - k)]
    · simp [Nat.sub_sub_self hkn, Nat.choose_symm hkn,
        Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      ring
    · intro b hb hbne
      have hneq : n - b ≠ k := by
        have hblt : b < n + 1 := Finset.mem_range.mp hb
        omega
      simp [hneq]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    have hdesc : n.descFactorial k = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hnk
    rw [hdesc]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hblt : b < n + 1 := Finset.mem_range.mp hb
    have hneq : n - b ≠ k := by omega
    simp [hneq]

/--
At finitely many distinct spectral points, all prescribed finite logarithmic
Mellin jet functionals are jointly linearly independent.
-/
theorem deningerMeyerStrongLogMellinFiniteJetLM_linearIndependent
    {r : ℕ} (rho : Fin r → ℂ) (hrho : Function.Injective rho)
    (mult : Fin r → ℕ) :
    LinearIndependent ℂ
      (fun q : GammaJetSlot mult =>
        deningerMeyerStrongLogMellinJetLM q.2 (rho q.1)) := by
  let N : ℕ := ∑ i, mult i
  let slot : Fin N ≃o GammaJetSlot mult :=
    gammaJetSlotOrderIso mult
  let f : Fin N →
      DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ :=
    fun q =>
      deningerMeyerStrongLogMellinJetLM
        ((slot q).2 : ℕ) (rho (slot q).1)
  have hf : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hrelation q0
    let F : ℝ → ℂ := fun t =>
      ∑ q : Fin N,
        c q * Complex.exp (rho (slot q).1 * (t : ℂ)) *
          (t : ℂ) ^ ((slot q).2 : ℕ)
    let FC : ℂ → ℂ := fun z =>
      ∑ q : Fin N,
        c q * Complex.exp (rho (slot q).1 * z) *
          z ^ ((slot q).2 : ℕ)
    have hFcont : Continuous F := by
      apply continuous_finsetSum
      intro q _hq
      exact
        (continuous_const.mul
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal))).mul
          (Complex.continuous_ofReal.pow _)
    have hFzeroAE : ∀ᵐ t ∂MeasureTheory.volume, F t = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
        hFcont.locallyIntegrable
      intro phi hphi hphiCompact
      let phiC : ℝ → ℂ := Complex.ofRealCLM ∘ phi
      have hphiCSmooth :
          ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) phiC :=
        Complex.ofRealCLM.contDiff.comp hphi
      have hphiCCompact : HasCompactSupport phiC :=
        hphiCompact.comp_left rfl
      let g : DeningerMeyerStrongLogTarget :=
        ⟨phiC,
          deningerMeyerStrongLogDecay_of_hasCompactSupport
            hphiCSmooth hphiCCompact⟩
      have hEval :=
        congrArg
          (fun L :
              DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ =>
            L g) hrelation
      have hEval' :
          (∑ q : Fin N,
            c q *
              iteratedDeriv ((slot q).2 : ℕ)
                (deningerMeyerStrongLogMellin g)
                (rho (slot q).1)) = 0 := by
        simpa only [
          f, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul, LinearMap.zero_apply,
          deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
          using hEval
      have hsum :
          (∑ q : Fin N,
            c q *
              ∫ t : ℝ,
                deningerMeyerStrongLogMellinJet
                  ((slot q).2 : ℕ) (rho (slot q).1) g t) = 0 := by
        calc
          _ = ∑ q : Fin N,
                c q *
                  iteratedDeriv ((slot q).2 : ℕ)
                    (deningerMeyerStrongLogMellin g)
                    (rho (slot q).1) := by
              apply Finset.sum_congr rfl
              intro q _hq
              rw [
                iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
                  g.property]
          _ = 0 := hEval'
      calc
        (∫ t : ℝ, phi t • F t) =
            ∫ t : ℝ,
              ∑ q : Fin N,
                c q *
                  deningerMeyerStrongLogMellinJet
                    ((slot q).2 : ℕ) (rho (slot q).1) g t := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          simp only [F, phiC, g,
            deningerMeyerStrongLogMellinJet,
            Function.comp_apply, Complex.ofRealCLM_apply,
            Complex.real_smul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _hq
          ring
        _ = ∑ q : Fin N,
              ∫ t : ℝ,
                c q *
                  deningerMeyerStrongLogMellinJet
                    ((slot q).2 : ℕ) (rho (slot q).1) g t := by
          apply MeasureTheory.integral_finsetSum
          intro q _hq
          exact
            (integrable_deningerMeyerStrongLogMellinJet
              g.property ((slot q).2 : ℕ)
              (rho (slot q).1)).const_mul (c q)
        _ = ∑ q : Fin N,
              c q *
                ∫ t : ℝ,
                  deningerMeyerStrongLogMellinJet
                    ((slot q).2 : ℕ) (rho (slot q).1) g t := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [MeasureTheory.integral_const_mul]
        _ = 0 := hsum
    have hFzero : F = 0 :=
      (Continuous.ae_eq_iff_eq MeasureTheory.volume
        hFcont continuous_zero).mp hFzeroAE
    have hFCanalytic :
        AnalyticOnNhd ℂ FC Set.univ := by
      apply DifferentiableOn.analyticOnNhd
      · exact (by fun_prop : Differentiable ℂ FC).differentiableOn
      · exact isOpen_univ
    have hFCzero : FC = 0 := by
      have hTendsto :
          Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact
            tendsto_nhdsWithin_of_tendsto_nhds
              Complex.continuous_ofReal.continuousAt
        · exact
            eventually_nhdsWithin_iff.mpr
              (Eventually.of_forall fun t ht =>
                Complex.ofReal_ne_zero.mpr ht)
      apply
        AnalyticOnNhd.eq_of_frequently_eq
          hFCanalytic analyticOnNhd_const
      apply hTendsto.frequently
      exact
        (Eventually.of_forall fun t => by
          have ht := congrFun hFzero t
          change FC (t : ℂ) = 0
          simpa only [FC, F, Pi.zero_apply] using ht).frequently
    let A : Matrix (Fin N) (Fin N) ℂ :=
      confluentPolynomialJetMatrix rho mult
        (fun n => Polynomial.X ^ (n : ℕ))
    have hdet : A.det ≠ 0 := by
      rw [show A =
          confluentPolynomialJetMatrix rho mult
            (fun n => Polynomial.X ^ (n : ℕ)) by rfl]
      rw [det_confluentPolynomialJetMatrix rho mult
        (fun n => Polynomial.X ^ (n : ℕ))]
      · apply mul_ne_zero
        · apply Finset.prod_ne_zero_iff.mpr
          intro i _hi
          apply Finset.prod_ne_zero_iff.mpr
          intro m _hm
          exact Nat.cast_ne_zero.mpr m.val.factorial_ne_zero
        · apply Finset.prod_ne_zero_iff.mpr
          intro i _hi
          apply Finset.prod_ne_zero_iff.mpr
          intro j hj
          apply pow_ne_zero
          exact
            sub_ne_zero.mpr
              (hrho.ne (ne_of_gt (Finset.mem_Ioi.mp hj)))
      · intro n
        exact Polynomial.natDegree_X_pow n.val
      · intro n
        exact Polynomial.monic_X.pow n.val
    have hrows :
        LinearIndependent ℂ (fun q => A q) :=
      Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hvecInj : Function.Injective A.vecMul :=
      Matrix.vecMul_injective_iff.mpr hrows
    have hczero : c = 0 := by
      apply hvecInj
      funext n
      have hderiv :=
        congrArg
          (fun G : ℂ → ℂ =>
            iteratedDeriv (n : ℕ) G 0) hFCzero
      have hderiv0 :
          iteratedDeriv (n : ℕ) FC 0 = 0 := by
        simpa using hderiv
      rw [show FC =
          fun z : ℂ =>
            ∑ q : Fin N,
              c q *
                (Complex.exp (rho (slot q).1 * z) *
                  z ^ ((slot q).2 : ℕ)) by
            funext z
            simp only [FC]
            apply Finset.sum_congr rfl
            intro q _hq
            ring] at hderiv0
      rw [iteratedDeriv_fun_sum (by
        intro q _hq
        fun_prop)] at hderiv0
      simp only [_root_.iteratedDeriv_const_mul_field,
        iteratedDeriv_cexp_mul_pow_zero] at hderiv0
      change
        (∑ q : Fin N,
          c q *
            ((Polynomial.derivative^[(slot q).2.val])
              (Polynomial.X ^ n.val)).eval
                (rho (slot q).1)) = 0 at hderiv0
      simpa only [
        Matrix.vecMul, dotProduct, Pi.zero_apply, mul_zero,
        zero_mul, Finset.sum_const_zero,
        A, confluentPolynomialJetMatrix,
        polynomialJetEvalMatrix, gammaJetSlotNode,
        gammaJetSlotOrder, slot]
        using hderiv0
    exact congrFun hczero q0
  have hcomp :=
    (linearIndependent_equiv slot.toEquiv.symm).mpr hf
  rw [show
      (fun q : GammaJetSlot mult =>
        deningerMeyerStrongLogMellinJetLM q.2 (rho q.1)) =
        f ∘ slot.toEquiv.symm by
      funext q
      simp only [Function.comp_apply, f]
      have hq : slot (slot.symm q) = q :=
        slot.apply_symm_apply q
      exact
        (congrArg
          (fun z : GammaJetSlot mult =>
            deningerMeyerStrongLogMellinJetLM z.2 (rho z.1))
          hq).symm]
  exact hcomp

/-- Named multiplicity-bounded jet slots over a finite Xi divisor set. -/
abbrev DeningerMeyerFiniteXiJetSlot
    (S : Finset XiDivisorSupport) :=
  Σ rho : ↥S, DeningerArithmeticJetIndex rho.1

/-- A chosen finite enumeration, used only inside the Wronskian proof. -/
noncomputable def deningerMeyerFiniteXiNodeEquiv
    (S : Finset XiDivisorSupport) :
    Fin (Fintype.card ↥S) ≃ ↥S :=
  (Fintype.equivFin ↥S).symm

abbrev deningerMeyerFiniteXiMultiplicity
    (S : Finset XiDivisorSupport)
    (i : Fin (Fintype.card ↥S)) : ℕ :=
  xiSupportMultiplicity (deningerMeyerFiniteXiNodeEquiv S i).1

/-- The confluent ordered slots are equivalent to the named finite Xi slots. -/
noncomputable def deningerMeyerFiniteXiJetSlotEquiv
    (S : Finset XiDivisorSupport) :
    GammaJetSlot (deningerMeyerFiniteXiMultiplicity S) ≃
      DeningerMeyerFiniteXiJetSlot S :=
  ofLex.trans
    (Equiv.sigmaCongr (deningerMeyerFiniteXiNodeEquiv S)
      (fun _ => Equiv.refl _))

/--
All finite Xi Mellin jets are jointly independent before quotienting by
Poisson boundaries.
-/
theorem deningerMeyerFiniteXiMellinJetLM_linearIndependent
    (S : Finset XiDivisorSupport) :
    LinearIndependent ℂ
      (fun q : DeningerMeyerFiniteXiJetSlot S =>
        deningerMeyerStrongLogMellinJetLM q.2 (q.1.1 : ℂ)) := by
  let node : Fin (Fintype.card ↥S) → ℂ :=
    fun i => ((deningerMeyerFiniteXiNodeEquiv S i).1 : ℂ)
  have hnode : Function.Injective node := by
    intro i j hij
    apply (deningerMeyerFiniteXiNodeEquiv S).injective
    apply Subtype.ext
    apply Subtype.ext
    simpa only [node] using hij
  have hflat :=
    deningerMeyerStrongLogMellinFiniteJetLM_linearIndependent
      node hnode (deningerMeyerFiniteXiMultiplicity S)
  apply
    (linearIndependent_equiv
      (deningerMeyerFiniteXiJetSlotEquiv S)).mp
  rw [show
      (fun q : DeningerMeyerFiniteXiJetSlot S =>
        deningerMeyerStrongLogMellinJetLM q.2 (q.1.1 : ℂ)) ∘
          deningerMeyerFiniteXiJetSlotEquiv S =
        (fun q :
            GammaJetSlot (deningerMeyerFiniteXiMultiplicity S) =>
          deningerMeyerStrongLogMellinJetLM
            q.2 (node q.1)) by
      funext q
      rfl]
  exact hflat

/--
All selected actual Xi jets remain jointly independent on literal Meyer
cohomology.
-/
theorem deningerMeyerFiniteXiSupportJetEvaluationLM_linearIndependent
    (S : Finset XiDivisorSupport) :
    LinearIndependent ℂ
      (fun q : DeningerMeyerFiniteXiJetSlot S =>
        deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hrelation q0
  have htarget :
      (∑ q : DeningerMeyerFiniteXiJetSlot S,
        c q •
          deningerMeyerStrongLogMellinJetLM
            q.2 (q.1.1 : ℂ)) = 0 := by
    ext g
    have hEval :=
      congrArg
        (fun L :
            DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ =>
          L (Submodule.Quotient.mk g)) hrelation
    simpa only [
      LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply,
      deningerMeyerXiSupportJetEvaluationLM_mk] using hEval
  exact
    Fintype.linearIndependent_iff.mp
      (deningerMeyerFiniteXiMellinJetLM_linearIndependent S)
      c htarget q0

/-- Named scalar packet over a finite Xi divisor set. -/
abbrev DeningerMeyerFiniteXiJetPacket
    (S : Finset XiDivisorSupport) :=
  DeningerMeyerFiniteXiJetSlot S → ℂ

/-- Simultaneous evaluation on every selected multiplicity-bounded Xi jet. -/
def deningerMeyerFiniteXiJetPacketLM
    (S : Finset XiDivisorSupport) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerFiniteXiJetPacket S :=
  LinearMap.pi fun q =>
    deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2

@[simp]
theorem deningerMeyerFiniteXiJetPacketLM_apply
    (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    deningerMeyerFiniteXiJetPacketLM S u q =
      deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2 u :=
  rfl

/--
Every named finite Xi jet packet has one literal Meyer representative.
-/
theorem deningerMeyerFiniteXiJetPacketLM_surjective
    (S : Finset XiDivisorSupport) :
    Function.Surjective (deningerMeyerFiniteXiJetPacketLM S) :=
  piMap_surjective_of_linearIndependent _
    (deningerMeyerFiniteXiSupportJetEvaluationLM_linearIndependent S)

/-- Exact simultaneous finite spectral quotient of Meyer cohomology. -/
def deningerMeyerFiniteXiJetPacketQuotEquiv
    (S : Finset XiDivisorSupport) :
    (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S)) ≃ₗ[ℂ]
      DeningerMeyerFiniteXiJetPacket S :=
  (deningerMeyerFiniteXiJetPacketLM S).quotKerEquivOfSurjective
    (deningerMeyerFiniteXiJetPacketLM_surjective S)

@[simp]
theorem deningerMeyerFiniteXiJetPacketQuotEquiv_mk
    (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketQuotEquiv S
        (Submodule.Quotient.mk u) =
      deningerMeyerFiniteXiJetPacketLM S u :=
  LinearMap.quotKerEquivOfSurjective_apply_mk
    (f := deningerMeyerFiniteXiJetPacketLM S)
    (deningerMeyerFiniteXiJetPacketLM_surjective S) u

/-- Direct sum of exact confluent Jordan flows on the named finite packet. -/
def deningerMeyerFiniteXiJetPacketFlow
    (S : Finset XiDivisorSupport) (c : ℝ) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ]
      DeningerMeyerFiniteXiJetPacket S where
  toFun x q :=
    ∑ i ∈ Finset.range (q.2.val + 1),
      (q.2.val.choose i : ℂ) *
        (c : ℂ) ^ i *
        Complex.exp ((c : ℂ) * (q.1.1 : ℂ)) *
        x
          ⟨q.1,
            ⟨q.2.val - i,
              lt_of_le_of_lt (Nat.sub_le q.2.val i) q.2.isLt⟩⟩
  map_add' x y := by
    funext q
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Literal Meyer dilation intertwines every selected Xi Jordan block. -/
theorem deningerMeyerFiniteXiJetPacketLM_flow
    (S : Finset XiDivisorSupport) (c : ℝ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerStrongLogCohomologyFlow c u) =
      deningerMeyerFiniteXiJetPacketFlow S c
        (deningerMeyerFiniteXiJetPacketLM S u) := by
  funext q
  exact
    deningerMeyerXiSupportJetEvaluationLM_flow
      q.1.1 q.2 c u

/-- The common finite-packet kernel is invariant under literal dilation. -/
theorem deningerMeyerFiniteXiJetPacketLM_ker_flow
    (S : Finset XiDivisorSupport) (c : ℝ)
    {u : DeningerMeyerStrongLogCohomology}
    (hu :
      u ∈ LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S)) :
    deningerMeyerStrongLogCohomologyFlow c u ∈
      LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S) := by
  rw [LinearMap.mem_ker] at hu ⊢
  rw [deningerMeyerFiniteXiJetPacketLM_flow, hu, map_zero]

/-- Dilation descended to the simultaneous finite Xi quotient. -/
def deningerMeyerFiniteXiJetPacketQuotientFlow
    (S : Finset XiDivisorSupport) (c : ℝ) :
    (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S)) →ₗ[ℂ]
      (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S)) :=
  (LinearMap.ker
    (deningerMeyerFiniteXiJetPacketLM S)).mapQ
      (LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S))
      (deningerMeyerStrongLogCohomologyFlow c)
      (by
        intro u hu
        exact
          deningerMeyerFiniteXiJetPacketLM_ker_flow
            S c hu)

/--
The simultaneous quotient equivalence conjugates descended Meyer dilation to
the direct sum of the selected full Jordan blocks.
-/
theorem deningerMeyerFiniteXiJetPacketQuotEquiv_flow
    (S : Finset XiDivisorSupport) (c : ℝ)
    (q :
      DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerFiniteXiJetPacketLM S)) :
    deningerMeyerFiniteXiJetPacketQuotEquiv S
        (deningerMeyerFiniteXiJetPacketQuotientFlow S c q) =
      deningerMeyerFiniteXiJetPacketFlow S c
        (deningerMeyerFiniteXiJetPacketQuotEquiv S q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
      simp only [
        deningerMeyerFiniteXiJetPacketQuotientFlow,
        Submodule.mapQ_apply,
        deningerMeyerFiniteXiJetPacketQuotEquiv_mk]
      exact deningerMeyerFiniteXiJetPacketLM_flow S c u

end

end RHTower
