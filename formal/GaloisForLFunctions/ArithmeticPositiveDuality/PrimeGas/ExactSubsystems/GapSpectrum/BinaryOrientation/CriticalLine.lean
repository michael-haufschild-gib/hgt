import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Labels
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! # The binary orientation of two copies detects isometric composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

/-- Complex two-copy heat amplitudes factor in the same basis as the total energy. -/
theorem pair_heat_factors (s : ℂ) (q : ℕ+ × ℕ+) :
    heat s q.1*heat s q.2 = heat (2*s) (basis q).1*heat s (basis q).2.1*heat s (basis q).2.2.val := by
  rw [← heat_mul,product_identity,pow_two,heat_mul,heat_mul,heat_mul,
    show (2:ℂ)*s = s+s by ring,heat_add]

/-- Square summability of the heat wave on the orientation factor of the two-copy normal form. -/
def orientationWave (s : ℂ) : Prop := Summable (fun j : SquarefreeLabel => ‖heat s j.val‖^2)

private def primeLabel (p : Nat.Primes) : SquarefreeLabel :=
  ⟨⟨p.val,p.property.pos⟩,Irreducible.squarefree p.property⟩

/-- The prime subseries already forces divergence of the squarefree wave at and below critical damping. -/
theorem orientation_wave_iff (s : ℂ) : orientationWave s ↔ 1/2 < s.re := by
  constructor
  · intro hs
    change Summable (fun j : SquarefreeLabel => ‖heat s j.val‖^2) at hs
    have hi : Function.Injective primeLabel := fun _ _ he =>
      Subtype.ext (congrArg (fun j : SquarefreeLabel => j.val.val) he)
    have hp := hs.comp_injective hi
    have hw (p : Nat.Primes) : ‖heat s (primeLabel p).val‖^2 = (p:ℝ)^(-2*s.re) := by
      rw [norm_heat,sq,← Real.exp_add,Real.rpow_def_of_pos (by exact_mod_cast p.property.pos)]
      apply congrArg Real.exp
      change -s.re*Real.log (p:ℝ)+ -s.re*Real.log (p:ℝ) = _
      ring
    have hsum : Summable (fun p : Nat.Primes => (p:ℝ)^(-2*s.re)) :=
      hp.congr hw
    have hlt := Nat.Primes.summable_rpow.mp hsum
    linarith only [hlt]
  · intro hs
    exact ((summable_heat_sq_iff s).mpr hs).comp_injective Subtype.val_injective

/-- Common occupations carry twice the single-copy energy, halving their summability threshold. -/
theorem common_wave_iff (s : ℂ) :
    (Summable fun k : ℕ+ => ‖heat (2*s) k‖^2) ↔ 1/4 < s.re := by
  rw [summable_heat_sq_iff,show (2:ℂ)*s = s+s by ring,Complex.add_re]
  constructor <;> intro h <;> linarith only [h]

/-- Loss of the binary wave at the smallest damping reached from the normalizable side singles out isometric order splitting. -/
theorem split_isometry_iff_orientation_boundary (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ¬orientationWave s ∧ ∀ δ : ℝ, 0 < δ → orientationWave (s+(δ:ℂ)) := by
  rw [split_isometric_iff]
  simp only [orientation_wave_iff,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro he
    exact ⟨he.le,fun δ hδ => by linarith only [he,hδ]⟩
  · rintro ⟨hle,hr⟩
    apply le_antisymm hle
    by_contra! h
    have he := hr (1/2-s.re) (sub_pos.mpr h)
    linarith only [he]

#print axioms pair_heat_factors
#print axioms orientation_wave_iff
#print axioms common_wave_iff
#print axioms split_isometry_iff_orientation_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
