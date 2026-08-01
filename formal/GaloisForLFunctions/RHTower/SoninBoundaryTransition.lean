import GaloisForLFunctions.RHTower.SoninBoundaryCorona
import GaloisForLFunctions.RHTower.SoninCouplingAdjointLimit
import GaloisForLFunctions.RHTower.SoninCouplingPartialUnitary

/-!
# The coupling and its adjoint are exact inverses on the boundary

The wavepacket family, its inverse dilate, and the two coupling images are bounded families, so
each has a boundary class.  The two asymptotic transition theorems say precisely that the
difference of the relevant families is norm-null, hence that the classes are equal.

So on these source-pointed classes the coupling sends the packet class to the dilate class and its
Hilbert adjoint sends the dilate class back, while both classes are nonzero: the packets survive a
completion that ordinary weak limits would erase.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- A class vanishes exactly when the family is norm-null. -/
theorem soninBoundaryClass_eq_zero_iff (f : soninBoundedFamilies) :
    soninBoundaryClass f = 0 ↔
      Tendsto (fun n => ‖(f : ℕ → evenSubspace) n‖) atTop (𝓝 0) := by
  have h := soninBoundaryClass_eq_iff f 0
  have hzero : soninBoundaryClass (0 : soninBoundedFamilies) = 0 := by
    rfl
  rw [hzero] at h
  refine h.trans (Iff.of_eq (congrArg (fun g => Tendsto g atTop (𝓝 0)) ?_))
  funext n
  simp

/-- The frequency-locked wavepacket family. -/
def soninPacketFamily (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (r : ℕ → ℝ) :
    soninBoundedFamilies :=
  ⟨fun n => soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)),
    ⟨2 * ‖soninBumpL2 b c hb hbc‖,
      fun n => norm_soninPacketL2_le b c hb hbc (2 * Real.pi * (r n * q))⟩⟩

/-- The inverse-dilated wavepacket family. -/
def soninDilatedPacketFamily (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (r : ℕ → ℝ)
    (hrpos : ∀ n, 0 < r n) : soninBoundedFamilies :=
  ⟨fun n => soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n),
    ⟨2 * ‖soninBumpL2 b c hb hbc‖,
      fun n =>
        norm_soninDilatedPacket_le b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)⟩⟩

/-- The coupling applied to the wavepacket family. -/
def soninCouplingFamily (a b c : ℝ) (hb : 0 < b) (hbc : b < c) (hab : a ≤ b) (q : ℝ)
    (r : ℕ → ℝ) (hrgt : ∀ n, 1 < r n) : soninBoundedFamilies :=
  ⟨fun n => evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
      (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))),
    ⟨2 * (2 * ‖soninBumpL2 b c hb hbc‖), fun n => by
      refine (norm_evenSoninApertureSuccessiveLayerTransition_apply_le hab hbc.le (hrgt n) _).trans
        ?_
      exact mul_le_mul_of_nonneg_left
        (norm_soninPacketL2_le b c hb hbc (2 * Real.pi * (r n * q))) (by norm_num)⟩⟩

/-- The adjoint coupling applied to the inverse-dilated family. -/
def soninAdjointCouplingFamily (a b c : ℝ) (hb : 0 < b) (hbc : b < c) (hab : a ≤ b) (q : ℝ)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) : soninBoundedFamilies :=
  ⟨fun n => ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
      (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)),
    ⟨2 * (2 * ‖soninBumpL2 b c hb hbc‖), fun n => by
      refine (norm_adjoint_evenSoninApertureSuccessiveLayerTransition_apply_le hab hbc.le
        (hrgt n) _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (norm_soninDilatedPacket_le b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n))
        (by norm_num)⟩⟩

/-- **`(20)`.**  The coupling family has the exact boundary value of the dilate class. -/
theorem soninBoundaryClass_soninCouplingFamily
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    soninBoundaryClass (soninCouplingFamily a b c hb hbc hab.le q r hrgt) =
      soninBoundaryClass (soninDilatedPacketFamily b c hb hbc q r hrpos) :=
  (soninBoundaryClass_eq_iff _ _).mpr
    (tendsto_norm_soninApertureCoupling_soninPacketEven_sub a b c ha hb hab hbc q haq hqb r
      hrpos hrgt hcr hr)

/-- **`(21)`.**  The adjoint coupling family has the exact boundary value of the packet class. -/
theorem soninBoundaryClass_soninAdjointCouplingFamily
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hr : Tendsto r atTop atTop) :
    soninBoundaryClass (soninAdjointCouplingFamily a b c hb hbc hab.le q r hrpos hrgt) =
      soninBoundaryClass (soninPacketFamily b c hb hbc q r) :=
  (soninBoundaryClass_eq_iff _ _).mpr
    (tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub a b c ha hb hbc q haq hqb
      r hrpos hrgt (fun n => pow_pos (hrpos n) 2) hr)

/-- The packet class is nonzero. -/
theorem soninBoundaryClass_soninPacketFamily_ne_zero
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    soninBoundaryClass (soninPacketFamily b c hb hbc q r) ≠ 0 := by
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hlim := tendsto_norm_soninPacketEven b c hb hbc (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  intro hzero
  have h0 := (soninBoundaryClass_eq_zero_iff _).mp hzero
  have := tendsto_nhds_unique h0 hlim
  exact absurd this.symm (ne_of_gt (sqrt_half_energy_pos b c hb hbc))

/-- The dilate class is nonzero. -/
theorem soninBoundaryClass_soninDilatedPacketFamily_ne_zero
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    soninBoundaryClass (soninDilatedPacketFamily b c hb hbc q r hrpos) ≠ 0 := by
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hlim := tendsto_norm_soninPacketEven b c hb hbc (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  intro hzero
  have h0 := (soninBoundaryClass_eq_zero_iff _).mp hzero
  have hdil : Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖)
      atTop (𝓝 0) := by
    refine h0.congr fun n => ?_
    exact norm_soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)
  have := tendsto_nhds_unique hdil hlim
  exact absurd this.symm (ne_of_gt (sqrt_half_energy_pos b c hb hbc))

/-- **The boundary transition is nontrivial.**  The coupling family carries a nonzero class, and
the adjoint carries it back: on these two classes the boundary operator and its Hilbert adjoint are
mutually inverse. -/
theorem soninBoundaryTransition_nontrivial
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    soninBoundaryClass (soninCouplingFamily a b c hb hbc hab.le q r hrgt) =
        soninBoundaryClass (soninDilatedPacketFamily b c hb hbc q r hrpos) ∧
      soninBoundaryClass (soninAdjointCouplingFamily a b c hb hbc hab.le q r hrpos hrgt) =
        soninBoundaryClass (soninPacketFamily b c hb hbc q r) ∧
      soninBoundaryClass (soninPacketFamily b c hb hbc q r) ≠ 0 ∧
      soninBoundaryClass (soninDilatedPacketFamily b c hb hbc q r hrpos) ≠ 0 :=
  ⟨soninBoundaryClass_soninCouplingFamily a b c ha hb hab hbc q haq hqb r hrpos hrgt hcr hr,
    soninBoundaryClass_soninAdjointCouplingFamily a b c ha hb hab hbc q haq hqb r hrpos hrgt hr,
    soninBoundaryClass_soninPacketFamily_ne_zero b c hb hbc q (ha.trans haq) r hr,
    soninBoundaryClass_soninDilatedPacketFamily_ne_zero b c hb hbc q (ha.trans haq) r hrpos hr⟩

end RHTower
