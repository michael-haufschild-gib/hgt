import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.BoundarySpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LocalPhaseContinuation
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # Prime modes and the partition function from the measured boundary

The nonzero contacts with the stability bound form a multiplicative monoid.
Its irreducible elements give the elementary modes, and its logarithmic
energy reproduces the Gibbs partition function.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private def measuredTrace (G : Propagator) : ℝ := (ContinuousLinearMap.opTrace (G.val^4)).re

/-- Readings calibrated by maximizing the measured trace over the same conserving class. -/
def calibratedReadings : Set (ℝ × ℝ) := {z | ∃ M G : Propagator,
  (∀ T : Propagator, measuredTrace T ≤ measuredTrace M) ∧
    z = (‖M.val-G.val‖,measuredTrace M-measuredTrace G)}

/-- The two experimental calibrations determine both the operator reference and the trace origin. -/
theorem calibratedReadings_eq : calibratedReadings = errorReadings := by
  have hd := (positive_fourth_iff criticalOperator).mpr rfl
  let D : Propagator := ⟨criticalOperator,hd.1,hd.2.1⟩
  have hmax : measuredTrace D = (riemannZeta 2).re := congrArg Complex.re hd.2.2
  have bound (T : Propagator) : measuredTrace T ≤ (riemannZeta 2).re := by
    have h := fourth_trace_bound ⟨T.val,T.property.2⟩
    rwa [fourthMoment_of_positive T.property.1] at h
  ext z
  constructor
  · rintro ⟨M,G,hm,rfl⟩
    have he := le_antisymm (bound M) (hmax ▸ hm D)
    have hl : traceLoss M.val = 0 := sub_eq_zero.mpr he.symm
    have h := (trace_stability M).2.2
    rw [hl] at h
    have hn := le_antisymm h (by positivity)
    have hD : M.val = criticalOperator := (sub_eq_zero.mp (norm_eq_zero.mp
      ((pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hn))).symm
    exact ⟨G,Prod.ext (by rw [hD]) (by change _ = measuredTrace M-measuredTrace G; rw [he]; rfl)⟩
  · rintro ⟨G,rfl⟩
    exact ⟨D,G,fun T => (bound T).trans_eq hmax.symm,Prod.ext rfl (by rw [hmax]; rfl)⟩

private theorem attenuation_one : attenuation 1 = 1 := by norm_num [attenuation,gain]

private theorem attenuation_mul (a b : ℕ+) : attenuation (a*b) = attenuation a*attenuation b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,critical_heat,critical_heat,critical_heat,heat_mul]

private theorem attenuation_injective : Function.Injective attenuation := by
  intro a b h
  have he : (a.val:ℝ) = (b.val:ℝ) := by
    rw [← gain_sq,← gain_sq]
    exact congrArg (fun r : ℝ => r^2) (inv_injective h)
  exact PNat.coe_injective (Nat.cast_injective he)

private theorem positive_contact (x : ℝ) :
    (0 < x ∧ (x,x^4) ∈ closure errorReadings) ↔ ∃ n : ℕ+, x = attenuation n := by
  rw [boundary_spectrum_iff]
  constructor
  · rintro ⟨hx,h⟩
    exact h.resolve_left hx.ne'
  · rintro ⟨n,rfl⟩
    exact ⟨attenuation_pos n,Or.inr ⟨n,rfl⟩⟩

/-- All positive fourth-power contacts of the measured error and trace. -/
def boundaryModes : Submonoid ℝ where
  carrier := {x | 0 < x ∧ (x,x^4) ∈ closure errorReadings}
  one_mem' := (positive_contact _).mpr ⟨1,attenuation_one.symm⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨a,rfl⟩ := (positive_contact x).mp hx
    obtain ⟨b,rfl⟩ := (positive_contact y).mp hy
    exact (positive_contact _).mpr ⟨a*b,(attenuation_mul a b).symm⟩

/-- Positive physical contacts, with ordinary multiplication, are the integer occupation monoid. -/
def boundaryModeEquiv : ℕ+ ≃* boundaryModes := by
  let e : ℕ+ →* boundaryModes := {
    toFun := fun n => ⟨attenuation n,(positive_contact _).mpr ⟨n,rfl⟩⟩
    map_one' := Subtype.ext attenuation_one
    map_mul' := fun a b => Subtype.ext (attenuation_mul a b) }
  exact MulEquiv.ofBijective e ⟨fun _ _ h => attenuation_injective (congrArg Subtype.val h),by
    intro x
    obtain ⟨n,hn⟩ := (positive_contact x.val).mp x.property
    exact ⟨n,Subtype.ext hn.symm⟩⟩

theorem boundaryModeEquiv_val (n : ℕ+) : (boundaryModeEquiv n).val = attenuation n := rfl

private theorem pnat_unit (n : ℕ+) : IsUnit n ↔ IsUnit n.val := by
  rw [Nat.isUnit_iff,PNat.coe_eq_one_iff]
  constructor
  · rintro ⟨u,rfl⟩
    apply PNat.coe_injective
    have h : (u.val:ℕ)*(u.inv:ℕ) = 1 := congrArg PNat.val u.val_inv
    exact Nat.dvd_one.mp ⟨(u.inv:ℕ),h.symm⟩
  · rintro rfl
    exact isUnit_one

private theorem pnat_irreducible (n : ℕ+) : Irreducible n ↔ n.val.Prime := by
  change Irreducible n ↔ Irreducible n.val
  constructor
  · intro h
    refine ⟨fun hu => h.not_isUnit ((pnat_unit n).mpr hu),?_⟩
    intro a b hab
    have hpos : 0 < a*b := hab ▸ n.pos
    let A : ℕ+ := ⟨a,Nat.pos_of_mul_pos_right hpos⟩
    let B : ℕ+ := ⟨b,Nat.pos_of_mul_pos_left hpos⟩
    have eqn : n = A*B := PNat.coe_injective hab
    exact (h.isUnit_or_isUnit eqn).imp (pnat_unit A).mp (pnat_unit B).mp
  · intro h
    refine ⟨fun hu => h.not_isUnit ((pnat_unit n).mp hu),?_⟩
    intro a b hab
    exact (h.isUnit_or_isUnit (congrArg PNat.val hab)).imp (pnat_unit a).mpr (pnat_unit b).mpr

/-- Prime occupations are precisely the multiplicatively irreducible measurements. -/
theorem irreducible_boundary_mode (x : boundaryModes) :
    Irreducible x ↔ (boundaryModeEquiv.symm x).val.Prime := by
  exact (MulEquiv.irreducible_iff (x := x) boundaryModeEquiv.symm).symm.trans (pnat_irreducible _)

/-- A finite prime occupation is determined uniquely by a positive contact. -/
def boundaryOccupationEquiv : (Nat.Primes →₀ ℕ) ≃ boundaryModes :=
  label.trans boundaryModeEquiv.toEquiv

theorem boundary_occupation_add (u v : Nat.Primes →₀ ℕ) :
    boundaryOccupationEquiv (u+v) = boundaryOccupationEquiv u*boundaryOccupationEquiv v := by
  change boundaryModeEquiv (label (u+v)) = boundaryModeEquiv (label u)*boundaryModeEquiv (label v)
  rw [label_add,map_mul]

def boundaryEnergy (x : boundaryModes) : ℝ := -2*Real.log x.val

theorem boundary_energy_eq (n : ℕ+) : boundaryEnergy (boundaryModeEquiv n) = energy n := by
  rw [boundaryEnergy,boundaryModeEquiv_val,attenuation,Real.log_inv,gain,Real.log_sqrt (Nat.cast_nonneg _),energy]
  ring

/-- Summing once over each positive measured contact recovers the full complex Gibbs trace. -/
theorem boundary_partition (s : {z : ℂ // 1 < z.re}) :
    ∑' x : boundaryModes, Complex.exp (-s.val*(boundaryEnergy x:ℂ)) = riemannZeta s.val := by
  rw [← boundaryModeEquiv.toEquiv.tsum_eq,← insertedPartition_one s,insertedPartition_eq_series]
  apply tsum_congr
  intro n
  change Complex.exp (-s.val*(boundaryEnergy (boundaryModeEquiv n):ℂ)) = (↑(1:Circle):ℂ)*heat s.val n
  rw [boundary_energy_eq,Circle.coe_one,one_mul]
  rfl

#print axioms calibratedReadings_eq
#print axioms boundaryModeEquiv
#print axioms irreducible_boundary_mode
#print axioms boundary_occupation_add
#print axioms boundary_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
