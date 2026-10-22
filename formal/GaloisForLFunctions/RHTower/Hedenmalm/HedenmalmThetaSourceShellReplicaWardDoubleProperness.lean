import GaloisForLFunctions.RHTower.WeightedCodiagonalDichotomy
import GaloisForLFunctions.RHTower.FrankensteinXiGreenStokesQuadraticGhostNormalForm
import GaloisForLFunctions.RHTower.HighExponentShellFusionConservation

/-!
# Theta-source shell-replica Ward-double properness

The literal high-exponent shells form infinitely many pairwise-disjoint positive arithmetic
sources carrying the same completed-zeta divisor.  On every shell label, this module places the
actual fixed-prime Deninger--Gamma quadratic ghost in the pinned theta harmonic line together with
its positive opposite-character curvature partner.

The resulting Ward double is silent after adding its two orientations, but its lifted history is
not silent.  Off the critical line, explicit finite shell packets converge to zero in the
canonical Hilbert sum while their lifted response converges to `(pinnedOne, -pinnedOne)`.  Thus the
shell-replica codiagonal is sequentially closable exactly on the critical line, and global
closability over all Xi divisor copies is equivalent to RH.

This is a formation/provenance theorem, not an RH proof: it identifies the exact global
properness law whose independent source derivation would force selection.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower

noncomputable section

/-- Semifinite counting trace on finite shell-label amplitudes. -/
def shellLabelCountingTrace : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ :=
  codiag (fun _ => 1)

/-- Positive density `x* x` in the diagonal shell-label algebra. -/
def shellLabelStarSquare (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  x.mapRange (fun z => (starRingEnd ℂ) z * z) (by simp)

/-- **Formation-generated GNS norm.** The positive counting trace of `x* x` is exactly the
canonical Hilbert direct-sum norm squared. -/
theorem shellLabelCountingTrace_starSquare (x : ℕ →₀ ℂ) :
    shellLabelCountingTrace (shellLabelStarSquare x) =
      ((‖(codiagEmbed x : lp (fun _ : ℕ => ℂ) 2)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [shellLabelCountingTrace, codiag_apply, norm_codiagEmbed_sq]
  have hsupp : (shellLabelStarSquare x).support = x.support := by
    ext n
    simp [shellLabelStarSquare, Finsupp.mem_support_iff,
      Finsupp.mapRange_apply, Complex.conj_mul']
  rw [hsupp]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  simp [shellLabelStarSquare, Finsupp.mapRange_apply, Complex.conj_mul']

/-- Successor action on the countable shell formation orbit. -/
def shellLabelSucc : ℕ ↪ ℕ where
  toFun n := n + 1
  inj' := by
    intro m n h
    exact Nat.add_right_cancel h

/-- Shift of a finite shell-label packet to its successor formations. -/
def shellLabelShift (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  x.embDomain shellLabelSucc

@[simp] theorem shellLabelShift_apply_succ (x : ℕ →₀ ℂ) (n : ℕ) :
    shellLabelShift x (n + 1) = x n := by
  exact Finsupp.embDomain_apply_self shellLabelSucc x n

@[simp] theorem shellLabelShift_apply_zero (x : ℕ →₀ ℂ) :
    shellLabelShift x 0 = 0 := by
  exact Finsupp.embDomain_notin_range shellLabelSucc x 0 (by
    rintro ⟨n, h⟩
    change n + 1 = 0 at h
    omega)

/-- Shell formation successor is an isometry for the counting-trace GNS norm. -/
theorem norm_codiagEmbed_shellLabelShift (x : ℕ →₀ ℂ) :
    ‖(codiagEmbed (shellLabelShift x) : lp (fun _ : ℕ => ℂ) 2)‖ =
      ‖(codiagEmbed x : lp (fun _ : ℕ => ℂ) 2)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_codiagEmbed_sq, norm_codiagEmbed_sq]
  rw [shellLabelShift, Finsupp.support_embDomain, Finset.sum_map]
  simp

/-- Counting trace is invariant under the shell formation successor. -/
theorem shellLabelCountingTrace_shift (x : ℕ →₀ ℂ) :
    shellLabelCountingTrace (shellLabelShift x) = shellLabelCountingTrace x := by
  rw [shellLabelCountingTrace, codiag_apply, codiag_apply,
    shellLabelShift, Finsupp.support_embDomain, Finset.sum_map]
  simp

end

end RHTower

namespace RHTower.HedenmalmThetaSource

noncomputable section

private def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Constant source weight read from the actual prime-two integral quadratic ghost. -/
def thetaXiQuadraticGhostOrbitWeight (rho : XiDivisorSupport) (_ : ℕ) : ℂ :=
  thetaXiIntegralQuadraticGhostCoefficient rho primeTwo

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- One marked shell-replica atom carrying the pinned harmonic source vector. -/
def thetaXiQuadraticGhostOrbitAtom (n : ℕ) : ℕ →₀ ThetaH :=
  Finsupp.single n pinnedOne

/-- The `n`th history label is the literal high-exponent shell `n + 12`. -/
def thetaXiQuadraticGhostOrbitShell (n : ℕ) : ℕ := n + 12

/-- Distinct history labels are literally disjoint arithmetic source sectors. -/
theorem thetaXiQuadraticGhostOrbitShell_orthogonal
    {m k n : ℕ} (hmk : m ≠ k) :
    shellIndicator (thetaXiQuadraticGhostOrbitShell m) n *
        shellIndicator (thetaXiQuadraticGhostOrbitShell k) n = 0 := by
  apply shellIndicator_mul_eq_zero_of_ne
  simpa [thetaXiQuadraticGhostOrbitShell] using hmk

/-- Every shell replica carries the unchanged completed-zeta divisor in the strict right
half-plane. -/
theorem thetaXiQuadraticGhostOrbitShell_divisorReplication
    (m : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt
        (fun z => completedRiemannZeta z *
          shellMultiplier (thetaXiQuadraticGhostOrbitShell m) z) s =
      analyticOrderAt completedRiemannZeta s := by
  exact analyticOrderAt_completedRiemannZeta_mul_shellMultiplier
    (by simp [thetaXiQuadraticGhostOrbitShell]) hs hs1

/-- Every finite shell-replica packet retains independent differential provenance even after the
coefficient field is enlarged by zeta and all of its derivatives. -/
theorem thetaXiQuadraticGhostOrbitShell_relativeDifferentialIndependent {n : ℕ} :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun i : Fin n =>
        relativeShellMultiplierUpperEndCarrier (finiteHighShellLevel i).1) :=
  finiteHighShell_relativeDifferentialIndependent

/-- The complete orbit weight vanishes exactly on the critical line. -/
theorem thetaXiQuadraticGhostOrbitWeight_eq_zero_iff (rho : XiDivisorSupport) :
    thetaXiQuadraticGhostOrbitWeight rho = 0 ↔ (rho : ℂ).re = 1 / 2 := by
  rw [funext_iff]
  constructor
  · intro h
    have h0 := h 0
    change (thetaXiIntegralQuadraticGhostCoefficient rho primeTwo : ℂ) = 0 at h0
    have hr : thetaXiIntegralQuadraticGhostCoefficient rho primeTwo = 0 := by
      exact_mod_cast h0
    exact (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho primeTwo).1 hr
  · intro hline n
    have hc := (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho primeTwo).2 hline
    simp [thetaXiQuadraticGhostOrbitWeight, hc]

/-- The constant orbit weight is square-summable exactly when its source ghost vanishes. -/
theorem summable_thetaXiQuadraticGhostOrbitWeight_sq_iff (rho : XiDivisorSupport) :
    Summable (fun n => ‖thetaXiQuadraticGhostOrbitWeight rho n‖ ^ (2 : ℕ)) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [show (fun n => ‖thetaXiQuadraticGhostOrbitWeight rho n‖ ^ (2 : ℕ)) =
      fun _ : ℕ => ‖(thetaXiIntegralQuadraticGhostCoefficient rho primeTwo : ℂ)‖ ^ (2 : ℕ) by
        rfl,
    summable_const_iff]
  constructor
  · intro h
    have hn : ‖(thetaXiIntegralQuadraticGhostCoefficient rho primeTwo : ℂ)‖ = 0 := by
      nlinarith [norm_nonneg
        (thetaXiIntegralQuadraticGhostCoefficient rho primeTwo : ℂ)]
    have hc : thetaXiIntegralQuadraticGhostCoefficient rho primeTwo = 0 := by
      exact_mod_cast (norm_eq_zero.mp hn)
    exact (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho primeTwo).1 hc
  · intro hline
    have hc := (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho primeTwo).2 hline
    simp [hc]

/-- Sequential closability of shell-replica recovery through the canonical Hilbert direct sum. -/
def ThetaXiQuadraticGhostOrbitClosable (rho : XiDivisorSupport) : Prop :=
  IsSequentiallyClosableBetween
    ((codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)).restrictScalars ℝ)
    ((codiagEmbed (H := ThetaH)).restrictScalars ℝ)

/-- Pointwise properness wall: shell-replica recovery is closable exactly on the critical line. -/
theorem thetaXiQuadraticGhostOrbitClosable_iff (rho : XiDivisorSupport) :
    ThetaXiQuadraticGhostOrbitClosable rho ↔ (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hclose
    by_contra hoff
    have hns : ¬ Summable (fun n => ‖thetaXiQuadraticGhostOrbitWeight rho n‖ ^ (2 : ℕ)) :=
      (summable_thetaXiQuadraticGhostOrbitWeight_sq_iff rho).not.mpr hoff
    exact (not_isSequentiallyClosableBetween_codiag hns pinnedOne_ne_zero) hclose
  · intro hline
    have hw : thetaXiQuadraticGhostOrbitWeight rho = 0 :=
      (thetaXiQuadraticGhostOrbitWeight_eq_zero_iff rho).2 hline
    unfold ThetaXiQuadraticGhostOrbitClosable IsSequentiallyClosableBetween
    intro u _hsource y hresponse
    have hT :
        ((codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)).restrictScalars ℝ) = 0 := by
      apply LinearMap.ext
      intro x
      rw [hw]
      simp [codiag_apply]
    rw [hT] at hresponse
    exact tendsto_nhds_unique hresponse tendsto_const_nhds

/-- Every marked shell atom recovers the literal source quadratic ghost. -/
theorem thetaXiQuadraticGhostOrbitAtom_recovery (rho : XiDivisorSupport) (n : ℕ) :
    codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)
        (thetaXiQuadraticGhostOrbitAtom n) =
      thetaXiIntegralQuadraticGhostVector rho primeTwo := by
  classical
  simp [codiag, thetaXiQuadraticGhostOrbitAtom,
    thetaXiQuadraticGhostOrbitWeight, thetaXiIntegralQuadraticGhostVector]
  rfl

/-- Each recovered shell ghost obeys exact ghost/positive-curvature conservation. -/
theorem thetaXiQuadraticGhostOrbitAtom_conservation
    (rho : XiDivisorSupport) (n : ℕ) :
    codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)
          (thetaXiQuadraticGhostOrbitAtom n) +
        thetaXiIntegralPairedCurvatureVector rho primeTwo = 0 := by
  rw [thetaXiQuadraticGhostOrbitAtom_recovery]
  exact thetaXiIntegralQuadraticGhostVector_add_pairedCurvatureVector rho primeTwo

/-- Lifted ghost/curvature Ward double before observer addition. -/
noncomputable def thetaXiQuadraticGhostOrbitWardDouble
    (rho : XiDivisorSupport) : (ℕ →₀ ThetaH) →ₗ[ℂ] ThetaH × ThetaH :=
  (codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)).prod
    (-(codiag (H := ThetaH) (thetaXiQuadraticGhostOrbitWeight rho)))

/-- Observer quotient adding the two Ward orientations. -/
def thetaXiQuadraticGhostOrbitWardQuotient :
    (ThetaH × ThetaH) →ₗ[ℂ] ThetaH :=
  LinearMap.fst ℂ ThetaH ThetaH + LinearMap.snd ℂ ThetaH ThetaH

/-- Observer-level conservation is identically silent for every finite lifted history. -/
theorem thetaXiQuadraticGhostOrbitWardQuotient_silent
    (rho : XiDivisorSupport) (x : ℕ →₀ ThetaH) :
    thetaXiQuadraticGhostOrbitWardQuotient
        (thetaXiQuadraticGhostOrbitWardDouble rho x) = 0 := by
  simp [thetaXiQuadraticGhostOrbitWardQuotient,
    thetaXiQuadraticGhostOrbitWardDouble]

/-- A basis atom reconstructs both literal orientations of the source Ward double. -/
theorem thetaXiQuadraticGhostOrbitWardDouble_atom_recovery
    (rho : XiDivisorSupport) (n : ℕ) :
    thetaXiQuadraticGhostOrbitWardDouble rho
        (thetaXiQuadraticGhostOrbitAtom n) =
      (thetaXiIntegralQuadraticGhostVector rho primeTwo,
        thetaXiIntegralPairedCurvatureVector rho primeTwo) := by
  apply Prod.ext
  · exact thetaXiQuadraticGhostOrbitAtom_recovery rho n
  · change -codiag (thetaXiQuadraticGhostOrbitWeight rho)
        (thetaXiQuadraticGhostOrbitAtom n) = _
    rw [thetaXiQuadraticGhostOrbitAtom_recovery,
      thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]

/-- Canonical normalized finite packet testing the lifted shell history. -/
noncomputable def thetaXiQuadraticGhostOrbitGraphNullPacket
    (rho : XiDivisorSupport) (N : ℕ) : ℕ →₀ ThetaH :=
  graphNullVector (thetaXiQuadraticGhostOrbitWeight rho) pinnedOne N

/-- Off the critical line, explicit finite packets vanish in source norm while their recovered
harmonic response stays nonzero. -/
theorem thetaXiQuadraticGhostOrbitGraphNullPacket_offCritical
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    Tendsto
        (fun N => codiagEmbed (thetaXiQuadraticGhostOrbitGraphNullPacket rho N) :
          ℕ → lp (fun _ : ℕ => ThetaH) 2)
        atTop (nhds 0) ∧
      Tendsto
        (fun N => codiag (thetaXiQuadraticGhostOrbitWeight rho)
          (thetaXiQuadraticGhostOrbitGraphNullPacket rho N))
        atTop (nhds pinnedOne) := by
  have hns : ¬ Summable (fun n => ‖thetaXiQuadraticGhostOrbitWeight rho n‖ ^ (2 : ℕ)) :=
    (summable_thetaXiQuadraticGhostOrbitWeight_sq_iff rho).not.mpr hoff
  have htop : Tendsto
      (fun N => ∑ m ∈ Finset.range N, ‖thetaXiQuadraticGhostOrbitWeight rho m‖ ^ (2 : ℕ))
      atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => sq_nonneg _)).mp hns
  have hsqrt : Tendsto
      (fun N => Real.sqrt
        (∑ m ∈ Finset.range N, ‖thetaXiQuadraticGhostOrbitWeight rho m‖ ^ (2 : ℕ)))
      atTop atTop :=
    Real.tendsto_sqrt_atTop.comp htop
  have heventually :
      ∀ᶠ N in atTop,
        0 < ∑ m ∈ Finset.range N, ‖thetaXiQuadraticGhostOrbitWeight rho m‖ ^ (2 : ℕ) :=
    htop.eventually_gt_atTop 0
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hzero : Tendsto
        (fun N => ‖pinnedOne‖ / Real.sqrt
          (∑ m ∈ Finset.range N, ‖thetaXiQuadraticGhostOrbitWeight rho m‖ ^ (2 : ℕ)))
        atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds hsqrt
    refine hzero.congr' ?_
    filter_upwards [heventually] with N hN
    exact (norm_codiagEmbed_graphNullVector
      (thetaXiQuadraticGhostOrbitWeight rho) pinnedOne hN).symm
  · refine (tendsto_const_nhds (x := pinnedOne) (f := atTop (α := ℕ))).congr' ?_
    filter_upwards [heventually] with N hN
    exact (codiag_graphNullVector
      (thetaXiQuadraticGhostOrbitWeight rho) pinnedOne (ne_of_gt hN)).symm

/-- The same graph-null packets have nonzero lifted Ward-double limit even though their observer
quotient is identically zero. -/
theorem thetaXiQuadraticGhostOrbitWardDouble_graphNullPacket_offCritical
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    Tendsto
        (fun N => thetaXiQuadraticGhostOrbitWardDouble rho
          (thetaXiQuadraticGhostOrbitGraphNullPacket rho N))
        atTop (nhds (pinnedOne, -pinnedOne)) := by
  have hresponse :=
    (thetaXiQuadraticGhostOrbitGraphNullPacket_offCritical rho hoff).2
  exact hresponse.prodMk_nhds hresponse.neg

/-- Global shell-replica properness over every actual Xi divisor copy. -/
def ThetaXiQuadraticGhostOrbitGloballyClosable : Prop :=
  ∀ rho : XiDivisorSupport, ThetaXiQuadraticGhostOrbitClosable rho

/-- Exact global selection interface: shell-replica properness is equivalent to RH. -/
theorem thetaXiQuadraticGhostOrbitGloballyClosable_iff_riemannHypothesis :
    ThetaXiQuadraticGhostOrbitGloballyClosable ↔ RiemannHypothesis := by
  constructor
  · intro hclose
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (thetaXiQuadraticGhostOrbitClosable_iff rho).1 (hclose rho)
  · intro hRH rho
    exact (thetaXiQuadraticGhostOrbitClosable_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Source-native replica/provenance capstone: literal orthogonal shell formation, unchanged
completed divisor, coefficient-faithful Ward-double recovery, quotient silence, and properness
selection all belong to one construction. -/
theorem thetaXiQuadraticGhostOrbit_sourceFormationPropernessLaw
    (rho : XiDivisorSupport) :
    (∀ x : ℕ →₀ ℂ,
      shellLabelCountingTrace (shellLabelStarSquare x) =
        ((‖(codiagEmbed x : lp (fun _ : ℕ => ℂ) 2)‖ ^ (2 : ℕ) : ℝ) : ℂ)) ∧
    (∀ x : ℕ →₀ ℂ,
      ‖(codiagEmbed (shellLabelShift x) : lp (fun _ : ℕ => ℂ) 2)‖ =
        ‖(codiagEmbed x : lp (fun _ : ℕ => ℂ) 2)‖) ∧
    (∀ x : ℕ →₀ ℂ,
      shellLabelCountingTrace (shellLabelShift x) = shellLabelCountingTrace x) ∧
    (∀ n : ℕ,
      DifferentialIndependent zetaUpperEndDifferentialField
        (fun i : Fin n =>
          relativeShellMultiplierUpperEndCarrier (finiteHighShellLevel i).1)) ∧
    (∀ (m k n : ℕ), m ≠ k →
      shellIndicator (thetaXiQuadraticGhostOrbitShell m) n *
          shellIndicator (thetaXiQuadraticGhostOrbitShell k) n = 0) ∧
    (∀ (m : ℕ) (s : ℂ), 1 / 2 < s.re → s ≠ 1 →
      analyticOrderAt
          (fun z => completedRiemannZeta z *
            shellMultiplier (thetaXiQuadraticGhostOrbitShell m) z) s =
        analyticOrderAt completedRiemannZeta s) ∧
    (∀ n : ℕ,
      thetaXiQuadraticGhostOrbitWardDouble rho
          (thetaXiQuadraticGhostOrbitAtom n) =
        (thetaXiIntegralQuadraticGhostVector rho primeTwo,
          thetaXiIntegralPairedCurvatureVector rho primeTwo)) ∧
    (∀ x : ℕ →₀ ThetaH,
      thetaXiQuadraticGhostOrbitWardQuotient
          (thetaXiQuadraticGhostOrbitWardDouble rho x) = 0) ∧
    (ThetaXiQuadraticGhostOrbitClosable rho ↔ (rho : ℂ).re = 1 / 2) ∧
    ((rho : ℂ).re ≠ 1 / 2 →
      Tendsto
          (fun N => codiagEmbed (thetaXiQuadraticGhostOrbitGraphNullPacket rho N) :
            ℕ → lp (fun _ : ℕ => ThetaH) 2)
          atTop (nhds 0) ∧
        Tendsto
          (fun N => thetaXiQuadraticGhostOrbitWardDouble rho
            (thetaXiQuadraticGhostOrbitGraphNullPacket rho N))
          atTop (nhds (pinnedOne, -pinnedOne))) := by
  exact ⟨shellLabelCountingTrace_starSquare,
    norm_codiagEmbed_shellLabelShift,
    shellLabelCountingTrace_shift,
    fun _ => thetaXiQuadraticGhostOrbitShell_relativeDifferentialIndependent,
    fun _ _ _ hmk => thetaXiQuadraticGhostOrbitShell_orthogonal hmk,
    fun m _ hs hs1 => thetaXiQuadraticGhostOrbitShell_divisorReplication m hs hs1,
    thetaXiQuadraticGhostOrbitWardDouble_atom_recovery rho,
    thetaXiQuadraticGhostOrbitWardQuotient_silent rho,
    thetaXiQuadraticGhostOrbitClosable_iff rho,
    fun hoff => ⟨
      (thetaXiQuadraticGhostOrbitGraphNullPacket_offCritical rho hoff).1,
      thetaXiQuadraticGhostOrbitWardDouble_graphNullPacket_offCritical rho hoff⟩⟩

end

end RHTower.HedenmalmThetaSource
