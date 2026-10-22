import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicLeftConnectionCovector

/-!
# Global left-coordinate Peierls incidence for the BM second harmonic

The canonical left connection covectors turn literal source-scaled regular and
Schwarz-complementary outer data into two coordinate-axis source packets. Over the finite-support
direct sum of all Xi copies, the exact negative complementary horizon exponent defines one fixed,
target-independent diagonal symplectic propagator. Its Peierls pairing is skew and pairs those
literal source packets to the BM boundary concomitant on every fibre and for every seed amplitude.

A pointwise diagonal cubic potential and algebraic square-root branch lift then realize the full
BM polarized cubic cut without inserting the requested target into the propagator. This closes the
previous source-incidence premise algebraically. It does not prove RH: source-fixed Schwarz
covariance of this global branch lift holds exactly on the critical line, and universal covariance
is equivalent to RH. Thus the residual HB burden is the physical Einstein--Teukolsky derivation of
that covariance, not radial incidence or Peierls algebra.

`[NEW] [GLOBAL PRODUCER] [EXACT INCIDENCE] [COVARIANCE CLASSIFICATION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

abbrev HBXiPeierlsPacket := XiZeroCopy →₀ ℂ

abbrev HBXiPeierlsCarrier := HBXiPeierlsPacket × HBXiPeierlsPacket

def hbXiPeierlsDot (x y : HBXiPeierlsPacket) : ℂ :=
  Finsupp.linearCombination ℂ (fun q => y q) x

theorem hbXiPeierlsDot_add_left (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsDot (x + y) z = hbXiPeierlsDot x z + hbXiPeierlsDot y z := by
  exact map_add (Finsupp.linearCombination ℂ fun q => z q) x y

theorem hbXiPeierlsDot_smul_left (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (c • x) y = c * hbXiPeierlsDot x y := by
  exact map_smul (Finsupp.linearCombination ℂ fun q => y q) c x

theorem hbXiPeierlsDot_neg_left (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (-x) y = -hbXiPeierlsDot x y := by
  simpa using hbXiPeierlsDot_smul_left (-1) x y

theorem hbXiPeierlsDot_single
    (q : XiZeroCopy) (c : ℂ) (y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (Finsupp.single q c) y = c * y q := by
  classical
  unfold hbXiPeierlsDot
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  · rfl
  · change (0 : ℂ) * y q = 0
    ring

theorem hbXiPeierlsDot_add_right (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsDot x (y + z) = hbXiPeierlsDot x y + hbXiPeierlsDot x z := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      simp only [hbXiPeierlsDot_add_left]
      rw [hf, hg]
      ring
  | single q c => simp [hbXiPeierlsDot, mul_add]

theorem hbXiPeierlsDot_smul_right (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot x (c • y) = c * hbXiPeierlsDot x y := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      simp only [hbXiPeierlsDot_add_left]
      rw [hf, hg]
      ring
  | single q d =>
      simp [hbXiPeierlsDot]
      ring

theorem hbXiPeierlsDot_comm (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot x y = hbXiPeierlsDot y x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp [hbXiPeierlsDot, Finsupp.linearCombination_apply]
  | add f g hf hg =>
      rw [hbXiPeierlsDot_add_left, hbXiPeierlsDot_add_right, hf, hg]
  | single q c =>
      unfold hbXiPeierlsDot
      rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index,
        Finsupp.linearCombination_apply, Finsupp.sum_eq_single q]
      · simp
        ring
      · intro r hr hne
        simp [hne]
      · simp
      · simp

def hbXiPeierlsPairing :
    HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun x y => hbXiPeierlsDot x.1 y.1 + hbXiPeierlsDot x.2 y.2)
    (by intro x y z; simp [hbXiPeierlsDot_add_left]; ring)
    (by intro c x y; simp [hbXiPeierlsDot_smul_left]; ring)
    (by intro x y z; simp [hbXiPeierlsDot_add_right]; ring)
    (by intro c x y; simp [hbXiPeierlsDot_smul_right]; ring)

@[simp]
theorem hbXiPeierlsPairing_apply (x y : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing x y =
      hbXiPeierlsDot x.1 y.1 + hbXiPeierlsDot x.2 y.2 := rfl

theorem hbXiPeierls_single_mul
    (q : XiZeroCopy) (c : ℂ) (y : HBXiPeierlsPacket) :
    Finsupp.single q c * y = Finsupp.single q (c * y q) := by
  classical
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

theorem hbXiPeierlsDot_mul_assoc
    (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsDot (x * y) z = hbXiPeierlsDot x (y * z) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      rw [add_mul, hbXiPeierlsDot_add_left, hbXiPeierlsDot_add_left, hf, hg]
  | single q c =>
      rw [hbXiPeierls_single_mul]
      rw [hbXiPeierlsDot_single, hbXiPeierlsDot_single]
      simp only [Finsupp.mul_apply]
      ring

/-- Pointwise polarization of one global diagonal cubic potential on Xi packets. -/
def hbXiPeierlsQuadraticResidual :
    HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier :=
  LinearMap.mk₂ ℂ
    (fun x y => (x.1 * y.1, x.2 * y.2))
    (by intro x y z; ext q <;> simp [add_mul])
    (by intro c x y; ext q <;> simp <;> ring)
    (by intro x y z; ext q <;> simp [mul_add])
    (by intro c x y; ext q <;> simp <;> ring)

@[simp]
theorem hbXiPeierlsQuadraticResidual_apply
    (x y : HBXiPeierlsCarrier) :
    hbXiPeierlsQuadraticResidual x y = (x.1 * y.1, x.2 * y.2) := rfl

theorem hbXiPeierlsQuadraticResidual_symmetric
    (x y : HBXiPeierlsCarrier) :
    hbXiPeierlsQuadraticResidual x y = hbXiPeierlsQuadraticResidual y x := by
  ext q <;> simp [mul_comm]

theorem hbXiPeierlsPairing_quadraticResidual_cyclic
    (x y z : HBXiPeierlsCarrier) :
    hbXiPeierlsPairing x (hbXiPeierlsQuadraticResidual y z) =
      hbXiPeierlsPairing z (hbXiPeierlsQuadraticResidual x y) := by
  simp only [hbXiPeierlsPairing_apply, hbXiPeierlsQuadraticResidual_apply]
  rw [← hbXiPeierlsDot_mul_assoc, ← hbXiPeierlsDot_mul_assoc,
    hbXiPeierlsDot_comm (x.1 * y.1) z.1,
    hbXiPeierlsDot_comm (x.2 * y.2) z.2]

/-- Chosen algebraic square root used only to lift literal quadratic residuals to branch fields. -/
def hbXiPeierlsSquareRoot (z : ℂ) : ℂ :=
  (IsAlgClosed.exists_eq_mul_self z).choose

theorem hbXiPeierlsSquareRoot_mul_self (z : ℂ) :
    hbXiPeierlsSquareRoot z * hbXiPeierlsSquareRoot z = z := by
  exact (IsAlgClosed.exists_eq_mul_self z).choose_spec.symm

theorem hbXiPeierlsSquareRoot_eq_zero_iff (z : ℂ) :
    hbXiPeierlsSquareRoot z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [← hbXiPeierlsSquareRoot_mul_self z, h]
    simp
  · intro h
    have hs : hbXiPeierlsSquareRoot z * hbXiPeierlsSquareRoot z = 0 :=
      (hbXiPeierlsSquareRoot_mul_self z).trans h
    exact mul_self_eq_zero.mp hs

def hbXiPeierlsRadialWeight (n : ℕ) (q : XiZeroCopy) : ℂ :=
  -d4BMPlusPlusComplementaryFrobeniusExponent n
    (d4BMXiMixedHorizonAngularMomentum q)

theorem hbXiPeierlsRadialWeight_ne_zero (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsRadialWeight n q ≠ 0 := by
  simp only [hbXiPeierlsRadialWeight, neg_ne_zero]
  exact d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

def hbXiPeierlsDiagonal (n : ℕ) (f : HBXiPeierlsPacket) : HBXiPeierlsPacket where
  support := f.support
  toFun := fun q => hbXiPeierlsRadialWeight n q * f q
  mem_support_toFun := by
    intro q
    simp [hbXiPeierlsRadialWeight_ne_zero n q]

@[simp]
theorem hbXiPeierlsDiagonal_apply (n : ℕ) (f : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsDiagonal n f q = hbXiPeierlsRadialWeight n q * f q := rfl

@[simp]
theorem hbXiPeierlsDiagonal_single
    (n : ℕ) (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsDiagonal n (Finsupp.single q c) =
      Finsupp.single q (hbXiPeierlsRadialWeight n q * c) := by
  classical
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

@[simp]
theorem hbXiPeierlsDiagonal_zero (n : ℕ) :
    hbXiPeierlsDiagonal n 0 = 0 := by
  ext q
  simp

theorem hbXiPeierlsDot_diagonal_single_single
    (n : ℕ) (q : XiZeroCopy) (c d : ℂ) :
    hbXiPeierlsDot (hbXiPeierlsDiagonal n (Finsupp.single q c))
        (Finsupp.single q d) = hbXiPeierlsRadialWeight n q * c * d := by
  classical
  rw [hbXiPeierlsDiagonal_single]
  unfold hbXiPeierlsDot
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  · simp
  · simp

theorem hbXiPeierlsDot_diagonal_comm
    (n : ℕ) (f g : HBXiPeierlsPacket) :
    hbXiPeierlsDot (hbXiPeierlsDiagonal n f) g =
      hbXiPeierlsDot f (hbXiPeierlsDiagonal n g) := by
  classical
  unfold hbXiPeierlsDot
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  change (∑ q ∈ f.support, hbXiPeierlsRadialWeight n q * f q * g q) =
    ∑ q ∈ f.support, f q * (hbXiPeierlsRadialWeight n q * g q)
  apply Finset.sum_congr rfl
  intro q hq
  ring

def hbXiPeierlsDiagonalLinear (n : ℕ) :
    HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket where
  toFun := hbXiPeierlsDiagonal n
  map_add' f g := by
    ext q
    simp [mul_add]
  map_smul' c f := by
    ext q
    simp
    ring

def hbXiPeierlsPropagator (n : ℕ) :
    HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier where
  toFun f := (-hbXiPeierlsDiagonal n f.2, hbXiPeierlsDiagonal n f.1)
  map_add' f g := by
    ext q <;> simp [mul_add, add_comm]
  map_smul' c f := by
    ext q <;> simp <;> ring

@[simp]
theorem hbXiPeierlsPropagator_apply (n : ℕ) (f : HBXiPeierlsCarrier) :
    hbXiPeierlsPropagator n f =
      (-hbXiPeierlsDiagonal n f.2, hbXiPeierlsDiagonal n f.1) := rfl

def hbXiPeierlsPlusSource (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  (Finsupp.single q (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q), 0)

def hbXiPeierlsMinusSource (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  (0, Finsupp.single q ((starRingEnd ℂ)
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q)))

def hbXiPeierlsPlusBranch (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  (Finsupp.single q (hbXiPeierlsSquareRoot
    (2 * d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q)), 0)

def hbXiPeierlsMinusBranch (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  (0, Finsupp.single q (hbXiPeierlsSquareRoot
    (2 * (starRingEnd ℂ)
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q))))

theorem d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hmix | hcarrier
    · exact (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mp hmix
    · exact False.elim
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q hcarrier)
  · intro h
    unfold d4BMXiSecondHarmonicPolarizedSourceAmplitude
    rw [(d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).mpr h]
    simp

theorem xiZeroCopyReflect_re_eq_one_sub (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
  rw [xiZeroCopyReflectEquiv_fst, xiZeroReflectEquiv_apply]
  norm_num

/-- The globally embedded literal branch lift obeys source-fixed Schwarz swap exactly on wall. -/
theorem hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsPlusBranch amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusBranch amplitude q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hfst := congrArg (fun x : HBXiPeierlsCarrier => x.1) h
    have heval := congrArg
      (fun f : HBXiPeierlsPacket => f (xiZeroCopyReflectEquiv q)) hfst
    simp only [hbXiPeierlsPlusBranch, hbXiPeierlsMinusBranch] at heval
    simp at heval
    have hsource :
        d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude
            (xiZeroCopyReflectEquiv q) = 0 := by
      have harg := (hbXiPeierlsSquareRoot_eq_zero_iff _).mp heval
      exact (mul_eq_zero.mp harg).resolve_left (by norm_num)
    have hrefline :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha
        (xiZeroCopyReflectEquiv q)).mp hsource
    rw [xiZeroCopyReflect_re_eq_one_sub] at hrefline
    linarith
  · intro hline
    have hrefline : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith
    have hq :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha q).mpr hline
    have href :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff ha
        (xiZeroCopyReflectEquiv q)).mpr hrefline
    unfold hbXiPeierlsPlusBranch hbXiPeierlsMinusBranch
    rw [hq, href]
    have hsqrt : hbXiPeierlsSquareRoot 0 = 0 :=
      (hbXiPeierlsSquareRoot_eq_zero_iff 0).mpr rfl
    simp [hsqrt]

theorem hbXiPeierlsMinusBranch_reflect_eq_plusBranch_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    hbXiPeierlsMinusBranch amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsPlusBranch amplitude q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have h := hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff ha
    (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopyReflectEquiv_apply_apply, eq_comm,
    xiZeroCopyReflect_re_eq_one_sub] at h
  constructor
  · intro hswap
    have := h.mp hswap
    linarith
  · intro hline
    apply h.mpr
    linarith

theorem hbXiPeierlsBranchSchwarzCovariant_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    (hbXiPeierlsPlusBranch amplitude (xiZeroCopyReflectEquiv q) =
          hbXiPeierlsMinusBranch amplitude q ∧
        hbXiPeierlsMinusBranch amplitude (xiZeroCopyReflectEquiv q) =
          hbXiPeierlsPlusBranch amplitude q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff ha,
    hbXiPeierlsMinusBranch_reflect_eq_plusBranch_iff ha, and_self]

/-- Universal Schwarz covariance of the target-independent global branch lift is exactly RH. -/
theorem forall_hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsPlusBranch amplitude (xiZeroCopyReflectEquiv q) =
        hbXiPeierlsMinusBranch amplitude q) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
      0).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).mpr
    exact (hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff ha q).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff ha q).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

theorem forall_hbXiPeierlsBranchSchwarzCovariant_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0) :
    ((∀ q : XiZeroCopy,
        hbXiPeierlsPlusBranch amplitude (xiZeroCopyReflectEquiv q) =
          hbXiPeierlsMinusBranch amplitude q) ∧
      (∀ q : XiZeroCopy,
        hbXiPeierlsMinusBranch amplitude (xiZeroCopyReflectEquiv q) =
          hbXiPeierlsPlusBranch amplitude q)) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (forall_hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff_rh ha).mp h.1
  · intro hRH
    constructor
    · exact (forall_hbXiPeierlsPlusBranch_reflect_eq_minusBranch_iff_rh ha).mpr hRH
    · intro q
      apply (hbXiPeierlsMinusBranch_reflect_eq_plusBranch_iff ha q).mpr
      exact xi_divisor_support_re_eq_half_of_rh hRH q.1

theorem hbXiPeierlsPlusBranch_quadraticResidual_eq_source
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
        (hbXiPeierlsPlusBranch amplitude q) = hbXiPeierlsPlusSource amplitude q := by
  classical
  apply Prod.ext
  · ext r
    by_cases h : r = q
    · subst r
      simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
        hbXiPeierlsPlusBranch, hbXiPeierlsPlusSource,
        hbXiPeierlsSquareRoot_mul_self]
    · simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
        hbXiPeierlsPlusBranch, hbXiPeierlsPlusSource, h]
  · ext r
    simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
      hbXiPeierlsPlusBranch, hbXiPeierlsPlusSource]

theorem hbXiPeierlsMinusBranch_quadraticResidual_eq_source
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
        (hbXiPeierlsMinusBranch amplitude q) = hbXiPeierlsMinusSource amplitude q := by
  classical
  apply Prod.ext
  · ext r
    simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
      hbXiPeierlsMinusBranch, hbXiPeierlsMinusSource]
  · ext r
    by_cases h : r = q
    · subst r
      simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
        hbXiPeierlsMinusBranch, hbXiPeierlsMinusSource,
        hbXiPeierlsSquareRoot_mul_self]
    · simp [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
        hbXiPeierlsMinusBranch, hbXiPeierlsMinusSource, h]

theorem d4BMXiPlusPlusRegularLeftConnectionCovector_scale
    (n : ℕ) (q : XiZeroCopy) (c source response : ℂ) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q
        (c * source) (c * response) =
      c * d4BMXiPlusPlusRegularLeftConnectionCovector n q source response := by
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
  dsimp only
  ring

theorem d4BMXiPlusPlusComplementaryLeftConnectionCovector_scale
    (n : ℕ) (q : XiZeroCopy) (c source response : ℂ) :
    d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
        (c * source) (c * response) =
      c * d4BMXiPlusPlusComplementaryLeftConnectionCovector n q source response := by
  unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  ring

/-- Literal regular `++` outer coefficients, transformed by canonical left covectors and embedded
in the global Xi direct sum. -/
def hbXiPeierlsPlusLeftSource
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let a := d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q
  (Finsupp.single q (d4BMXiPlusPlusRegularLeftConnectionCovector n q
      (a * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
      (a * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi)),
    Finsupp.single q (d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
      (a * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
      (a * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi)))

/-- Literal Schwarz-complementary `--` outer coefficients, conjugated as in the boundary
concomitant, transformed by canonical left covectors, and embedded globally. -/
def hbXiPeierlsMinusLeftSource
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) : HBXiPeierlsCarrier :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let a := d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q
  (Finsupp.single q (d4BMXiPlusPlusRegularLeftConnectionCovector n q
      ((starRingEnd ℂ) (a * (starRingEnd ℂ)
        (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi)))
      ((starRingEnd ℂ) (a * (starRingEnd ℂ)
        (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi)))),
    Finsupp.single q (d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
      ((starRingEnd ℂ) (a * (starRingEnd ℂ)
        (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi)))
      ((starRingEnd ℂ) (a * (starRingEnd ℂ)
        (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi)))))

theorem hbXiPeierlsPlusLeftSource_eq
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsPlusLeftSource n amplitude q = hbXiPeierlsPlusSource amplitude q := by
  classical
  unfold hbXiPeierlsPlusLeftSource hbXiPeierlsPlusSource
  dsimp only
  rw [d4BMXiPlusPlusRegularLeftConnectionCovector_scale,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_scale,
    d4BMXiPlusPlusRegularLeftConnectionCovector_regular_eq_one,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_regular_eq_zero]
  ext r <;> simp

theorem hbXiPeierlsMinusLeftSource_eq
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsMinusLeftSource n amplitude q = hbXiPeierlsMinusSource amplitude q := by
  classical
  unfold hbXiPeierlsMinusLeftSource hbXiPeierlsMinusSource
  dsimp only
  simp only [map_mul, starRingEnd_self_apply]
  rw [d4BMXiPlusPlusRegularLeftConnectionCovector_scale,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_scale,
    d4BMXiPlusPlusRegularLeftConnectionCovector_complementary_eq_zero,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_complementary_eq_one]
  ext r <;> simp

theorem hbXiPeierlsSourcePairing_skew
    (n : ℕ) (f g : HBXiPeierlsCarrier) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n) f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n) g f := by
  simp only [d4GaugeFixedTeukolskyPeierlsSourcePairing,
    hbXiPeierlsPairing_apply, hbXiPeierlsPropagator_apply,
    hbXiPeierlsDot_neg_left]
  rw [hbXiPeierlsDot_comm (hbXiPeierlsDiagonal n g.2) f.1,
    hbXiPeierlsDot_comm (hbXiPeierlsDiagonal n g.1) f.2,
    hbXiPeierlsDot_diagonal_comm, hbXiPeierlsDot_diagonal_comm]
  ring

theorem hbXiPeierls_sourcePairing_eq
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusSource amplitude q)
        (hbXiPeierlsMinusSource amplitude q) =
      hbXiPeierlsRadialWeight n q *
        Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q) := by
  classical
  change hbXiPeierlsDot (0 : HBXiPeierlsPacket) 0 +
      hbXiPeierlsDot (hbXiPeierlsDiagonal n
        (Finsupp.single q (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q)))
        (Finsupp.single q ((starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q))) = _
  rw [hbXiPeierlsDot_diagonal_single_single]
  simp only [hbXiPeierlsDot, map_zero, zero_add]
  rw [← Complex.mul_conj]
  ring

theorem d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant_eq_radialWeight_mul_normSq
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q =
      hbXiPeierlsRadialWeight n q *
        Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude amplitude q) := by
  rw [← d4BMXiSecondHarmonicSourceScaledPolarizedCurrent_eq_boundaryConcomitant
    n amplitude q (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num),
    d4BMXiSecondHarmonicSourceScaledPolarizedCurrent_eq,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent
      n (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)
      (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  simp only [hbXiPeierlsRadialWeight]
  ring

theorem hbXiPeierls_BM_source_incidence
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusSource amplitude q)
        (hbXiPeierlsMinusSource amplitude q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q := by
  rw [hbXiPeierls_sourcePairing_eq,
    d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant_eq_radialWeight_mul_normSq]

theorem hbXiPeierls_BM_quadraticSource_incidence
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
          (hbXiPeierlsPlusBranch amplitude q))
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
          (hbXiPeierlsMinusBranch amplitude q)) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q := by
  rw [hbXiPeierlsPlusBranch_quadraticResidual_eq_source,
    hbXiPeierlsMinusBranch_quadraticResidual_eq_source]
  exact hbXiPeierls_BM_source_incidence n amplitude q

/-- Exact global Peierls algebra realizes the BM polarized cut without scaling the propagator by
the requested BM target. The remaining physical issue is Schwarz covariance of the branch lift. -/
theorem hbXiPeierls_phaseNormalizedCubicCut_eq_BM_candidate
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
        hbXiPeierlsPairing hbXiPeierlsQuadraticResidual
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusBranch amplitude q)
        (hbXiPeierlsMinusBranch amplitude q) =
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n amplitude q z := by
  calc
    _ = 2 * d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
          (hbXiPeierlsPlusBranch amplitude q))
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual hbXiPeierlsQuadraticResidual
          (hbXiPeierlsMinusBranch amplitude q)) :=
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
        hbXiPeierlsPairing hbXiPeierlsQuadraticResidual
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusBranch amplitude q)
        (hbXiPeierlsMinusBranch amplitude q)
        hbXiPeierlsQuadraticResidual_symmetric
        hbXiPeierlsPairing_quadraticResidual_cyclic
        (hbXiPeierlsSourcePairing_skew n)
    _ = 2 * d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q := by
      rw [hbXiPeierls_BM_quadraticSource_incidence]
    _ = _ := (d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_two_mul_boundaryConcomitant
      n amplitude q hz0 hz1).symm

/-- One target-independent global radial Peierls operator pairs the literal left-coordinate
Einstein--Teukolsky source states to the exact BM boundary concomitant on every Xi fibre. -/
theorem hbXiPeierls_BM_leftSource_incidence
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusLeftSource n amplitude q)
        (hbXiPeierlsMinusLeftSource n amplitude q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q := by
  rw [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsMinusLeftSource_eq]
  exact hbXiPeierls_BM_source_incidence n amplitude q

end

end RHTower
