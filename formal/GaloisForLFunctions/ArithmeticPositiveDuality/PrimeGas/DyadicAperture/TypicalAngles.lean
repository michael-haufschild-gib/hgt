import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Antipode
import GaloisForLFunctions.HTGeometry.PaperCirclePhysicalHeight
import GaloisForLFunctions.HTGeometry.LineScalingL2
import GaloisForLFunctions.RHTower.GaussQuasiInnerSquare
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Dyadic phases at almost every physical time

Almost every orbit comes arbitrarily close to the antipode and avoids
the antipode itself. The covering map and a nonzero energy dilation
transfer both statements to almost every real sampling time.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture

open MeasureTheory Set Filter

private abbrev Turns := AddCircle (1:ℝ)

private def read (x : Turns) := angle (AddCircle.toCircle x)

private theorem continuous_read : Continuous read := by
  unfold read angle
  fun_prop

private def opposite : Turns := ((1/2:ℝ) : Turns)

private theorem opposite_phase : AddCircle.toCircle opposite = Circle.exp Real.pi := by
  rw [opposite,AddCircle.toCircle_apply_mk]
  congr 1
  ring

private theorem read_opposite : read opposite = Real.pi :=
  (congrArg angle opposite_phase).trans (exp_angle _ ⟨Real.pi_pos.le,le_rfl⟩)

private theorem read_pi_iff (x : Turns) : read x = Real.pi ↔ x = opposite := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle (one_ne_zero : (1:ℝ) ≠ 0)
    exact ((angle_pi_iff _).mp h).trans ((angle_pi_iff _).mp read_opposite).symm
  · rintro rfl
    exact read_opposite

private def trapped (q : ℝ) : Set Turns := {x | ∀ k : ℕ, read ((2^k:ℕ) • x) ≤ q}

private theorem closed_trapped (q : ℝ) : IsClosed (trapped q) := by
  have he : trapped q = ⋂ k : ℕ, {x : Turns | read ((2^k:ℕ) • x) ≤ q} := by
    ext x
    simp only [trapped,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun k => isClosed_le (continuous_read.comp (continuous_nsmul (2^k))) continuous_const

private theorem escape (q : ℝ) (hq : q < Real.pi) : ∀ᵐ x : Turns, ∃ k : ℕ, q < read ((2^k:ℕ) • x) := by
  have inv : trapped q ⊆ (fun x : Turns => (2:ℕ) • x) ⁻¹' trapped q := by
    intro x hx k
    change read ((2^k:ℕ) • ((2:ℕ) • x)) ≤ q
    rw [smul_smul,← pow_succ]
    exact hx (k+1)
  have hh := (AddCircle.ergodic_nsmul (T := (1:ℝ)) (by norm_num : 1 < (2:ℕ))).ae_empty_or_univ_of_ae_le_preimage
    (closed_trapped q).measurableSet.nullMeasurableSet (LE.le.eventuallyLE inv)
  rcases hh with hempty | hfull
  · have avoid : ∀ᵐ x : Turns, x ∉ trapped q := by
      apply ae_iff.mpr
      simpa using ae_eq_empty.mp hempty
    filter_upwards [avoid] with x hx
    by_contra! hn
    exact hx hn
  · exfalso
    have sub : {x : Turns | q < read x} ⊆ (trapped q)ᶜ := by
      intro x hx ht
      exact (not_lt.mpr (by simpa only [pow_zero,one_smul] using ht 0)) hx
    have hz := measure_mono_null sub (ae_eq_univ.mp hfull)
    have nonempty : {x : Turns | q < read x}.Nonempty := ⟨opposite,hq.trans_eq read_opposite.symm⟩
    exact ((isOpen_lt continuous_const continuous_read).measure_pos volume nonempty).ne' hz

/-- A dyadic phase approaches the antipode arbitrarily closely without ever reaching it. -/
def Approaches (z : Circle) : Prop :=
  (∀ θ : ℝ, θ < Real.pi → ∃ k : ℕ, θ < angle (z^(2^k : ℕ))) ∧
  ∀ k : ℕ, angle (z^(2^k : ℕ)) < Real.pi

private theorem avoids_opposite (k : ℕ) : ∀ᵐ x : Turns, (2^k:ℕ) • x ≠ opposite := by
  have h : ∀ᵐ x : Turns, x ≠ opposite :=
    measure_eq_zero_iff_ae_notMem.mp (_root_.RHTower.volume_singleton_addCircle opposite)
  cases k with
  | zero => simpa only [pow_zero,one_smul] using h
  | succ n =>
    have hp : 1 < (2:ℕ)^(n+1) := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero _)
    exact (AddCircle.ergodic_nsmul (T := (1:ℝ)) hp).quasiMeasurePreserving.ae
      (p := fun y : Turns => y ≠ opposite) h

private theorem typical_turn : ∀ᵐ x : Turns, Approaches (AddCircle.toCircle x) := by
  have esc (q : ℚ) : ∀ᵐ x : Turns, (q:ℝ) < Real.pi → ∃ k : ℕ, (q:ℝ) < read ((2^k:ℕ) • x) := by
    by_cases hq : (q:ℝ) < Real.pi
    · exact (escape _ hq).mono fun _ hx _ => hx
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [ae_all_iff.mpr esc,ae_all_iff.mpr avoids_opposite] with x he ha
  constructor
  · intro θ hθ
    obtain ⟨q,hq,hqπ⟩ := exists_rat_btwn hθ
    obtain ⟨k,hk⟩ := he q hqπ
    exact ⟨k,hq.trans (by simpa only [read,AddCircle.toCircle_nsmul] using hk)⟩
  · intro k
    rw [← AddCircle.toCircle_nsmul]
    exact lt_of_le_of_ne (angle_mem _).2 (fun h => ha k ((read_pi_iff _).mp h))

/-- Every nonzero logarithmic gap sees the two antipodal properties at almost every real time. -/
theorem typical_gap (d : {d : ℝ // d ≠ 0}) :
    ∀ᵐ t : ℝ, Approaches (Circle.exp (t*d.val)) := by
  have hh : ∀ᵐ x : Turns ∂AddCircle.haarAddCircle, Approaches (AddCircle.toCircle x) := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using typical_turn
  have lifted := (HTGeometry.paperCirclePhysicalHeight_quasiMeasurePreserving 1).ae hh
  have hc : d.val/(2*Real.pi) ≠ 0 := div_ne_zero d.property (mul_pos (by norm_num) Real.pi_pos).ne'
  have h := (HTGeometry.quasiMeasurePreserving_const_mul hc).ae lifted
  filter_upwards [h] with t ht
  change Approaches (AddCircle.toCircle (((d.val/(2*Real.pi)*t:ℝ)) : Turns)) at ht
  rw [AddCircle.toCircle_apply_mk,show 2*Real.pi/1*(d.val/(2*Real.pi)*t) = t*d.val by field_simp] at ht
  exact ht

#print axioms typical_gap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture
