import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.TypicalAngles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.NetworkHeat
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.BinarySectors

/-!
# Almost-sure jump of the measured partition

A common full-measure set of sampling times works for all occupations
and all apertures. Each proper aperture gives the diagonal partition.
At the maximal strict aperture every pair passes and the partition squares.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary

open SampledClocks MeasureTheory Filter

private theorem energy_injective : Function.Injective energy := by
  intro a b h
  have he := congrArg Real.exp h
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) he)

private theorem identity_phase (t : ℝ) {x : Word} (hx : equal x) : (binary t).phase () x = 1 := by
  change Circle.exp (t*(energy (x false)-energy (x true))) = 1
  rw [hx,sub_self,mul_zero,Circle.exp_zero]

private theorem angle_one : angle 1 = 0 := by simpa using exp_angle 0 ⟨le_rfl,Real.pi_pos.le⟩

/-- Proper apertures select exactly equal labels, while the maximal aperture accepts every word. -/
theorem typical_sectors : ∀ᵐ t : ℝ,
    (∀ θ : Set.Ioo 0 Real.pi, measured t θ.val = equal) ∧ measured t Real.pi = full := by
  have hg (x : Word) : ∀ᵐ t : ℝ, ¬equal x → Approaches ((binary t).phase () x) := by
    by_cases h : equal x
    · exact Eventually.of_forall fun _ hn => (hn h).elim
    · have hn : energy (x false)-energy (x true) ≠ 0 := sub_ne_zero.mpr (fun he => h (energy_injective he))
      exact (typical_gap ⟨_,hn⟩).mono fun _ ht _ => ht
  filter_upwards [ae_all_iff.mpr hg] with t ht
  constructor
  · intro θ
    let u : Set.Icc 0 Real.pi := ⟨θ.val,θ.property.1.le,θ.property.2.le⟩
    funext x
    apply propext
    change (binary t).Repeated (Real.sqrt (aperture u.val)) x ↔ equal x
    rw [repeated_angles (binary t) u]
    constructor
    · intro h
      by_contra hn
      obtain ⟨k,hk⟩ := (ht x hn).1 _ θ.property.2
      exact (not_lt.mpr hk.le) (h () k)
    · intro hx e k
      cases e
      rw [identity_phase t hx,one_pow,angle_one]
      exact θ.property.1
  · funext x
    apply propext
    refine iff_of_true ?_ trivial
    apply (repeated_angles (binary t) (⟨Real.pi,Real.pi_pos.le,le_rfl⟩ : Set.Icc 0 Real.pi) x).mpr
    rintro ⟨⟩ k
    by_cases hx : equal x
    · rw [identity_phase t hx,one_pow,angle_one]
      exact Real.pi_pos
    · exact (ht x hx).2 k

/-- Exact trace-class domain and operator trace on that domain. -/
def PartitionLaw (P : Word → Prop) (β : ℝ) (F : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, HasSectorHeat P s ↔ β < s.re) ∧
    ∀ s : {z : ℂ // AbsoluteHeat P z}, ContinuousLinearMap.opTrace (sectorHeat P s) = F s.val

theorem typical_partitions : ∀ᵐ t : ℝ,
    (∀ θ : Set.Ioo 0 Real.pi, PartitionLaw (measured t θ.val) (1/2) (fun s => riemannZeta (2*s))) ∧
      PartitionLaw (measured t Real.pi) 1 (fun s => riemannZeta s ^ 2) := by
  filter_upwards [typical_sectors] with t ht
  constructor
  · intro θ
    rw [ht.1 θ]
    refine ⟨equal_heat,fun s => (operator_trace _ s).trans ?_⟩
    exact equal_partition ⟨s.val,(equal_heat _).mp ((sectorHeat_iff _ _).mpr s.property)⟩
  · rw [ht.2]
    refine ⟨full_heat,fun s => (operator_trace _ s).trans ?_⟩
    exact full_partition ⟨s.val,(full_heat _).mp ((sectorHeat_iff _ _).mpr s.property)⟩

#print axioms typical_sectors
#print axioms typical_partitions

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Binary
