import GaloisForLFunctions.HTGeometry.BohrHullFrequency

/-!
# Characters on integer combinations of frequencies

A unimodular multiplicative function on `ℝ` turns a finite integer combination of reals into the
corresponding product of powers.  Applied to the exponentials `t ↦ e^{i μ t}` and transported to the
Bohr hull by density, this says that the hull character attached to an integer combination of
frequencies is the corresponding product of powers of the individual hull characters.

This is what reduces a phase prescription on an arbitrary finite set of frequencies — where integer
relations are allowed — to a prescription on a rationally independent set, where Kronecker's theorem
applies.
-/

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open Finset

section Hom

variable {ω : ℝ → ℂ} (hmul : ∀ a b, ω (a + b) = ω a * ω b) (hnorm : ∀ a, ‖ω a‖ = 1)

include hmul hnorm

theorem char_zero_eq_one : ω 0 = 1 := by
  have h := hmul 0 0
  rw [add_zero] at h
  have hne : ω 0 ≠ 0 := by
    intro hz
    have := hnorm 0
    rw [hz, norm_zero] at this
    norm_num at this
  field_simp at h
  exact h.symm

theorem char_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ω (∑ i ∈ s, g i) = ∏ i ∈ s, ω (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using char_zero_eq_one hmul hnorm
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, hmul, ih]

theorem char_zsmul (n : ℤ) (a : ℝ) : ω ((n : ℝ) * a) = (ω a) ^ n := by
  have hne : ∀ b : ℝ, ω b ≠ 0 := by
    intro b hb
    have := hnorm b
    rw [hb, norm_zero] at this
    norm_num at this
  induction n using Int.induction_on with
  | zero => simpa using char_zero_eq_one hmul hnorm
  | succ k ih =>
      have hcast : ((k : ℝ) + 1) * a = (k : ℝ) * a + a := by ring
      push_cast
      push_cast at ih
      rw [hcast, hmul, ih, zpow_add₀ (hne a)]
      simp
  | pred k ih =>
      have hcast : ((-(k : ℝ)) - 1) * a = (-(k : ℝ)) * a + (-a) := by ring
      push_cast
      push_cast at ih
      rw [hcast, hmul, ih]
      have hinv : ω (-a) = (ω a)⁻¹ := by
        have h1 : ω a * ω (-a) = 1 := by
          rw [← hmul]
          simpa using char_zero_eq_one hmul hnorm
        have h2 : ω a ≠ 0 := hne a
        field_simp
        linear_combination h1
      rw [hinv, zpow_sub₀ (hne a)]
      field_simp

theorem char_intCombination {k : ℕ} (b : Fin k → ℝ) (n : Fin k → ℤ) :
    ω (∑ i, (n i : ℝ) * b i) = ∏ i, (ω (b i)) ^ (n i) := by
  rw [char_sum hmul hnorm]
  exact Finset.prod_congr rfl fun i _ => char_zsmul hmul hnorm (n i) (b i)

end Hom

section Hull

open HTGeometry

variable {f : ℝ →ᵇ ℂ}

theorem isBohrHullFrequency_intCombination {k : ℕ} {b : Fin k → ℝ}
    (hb : ∀ i, IsBohrHullFrequency f (b i)) (n : Fin k → ℤ) :
    IsBohrHullFrequency f (∑ i, (n i : ℝ) * b i) := by
  rw [← mem_bohrHullFrequencies]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have hmem : b i ∈ bohrHullFrequencies f := mem_bohrHullFrequencies.mpr (hb i)
  have := AddSubgroup.zsmul_mem (bohrHullFrequencies f) hmem (n i)
  rwa [zsmul_eq_mul] at this

theorem expChar_add_frequency (mu nu t : ℝ) : expChar (mu + nu) t = expChar mu t * expChar nu t := by
  simp only [expChar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem bohrHullChar_intCombination
    {k : ℕ} {b : Fin k → ℝ} (hb : ∀ i, IsBohrHullFrequency f (b i)) (n : Fin k → ℤ)
    (x : BohrHull f) :
    bohrHullChar f (∑ i, (n i : ℝ) * b i) x = ∏ i, (bohrHullChar f (b i) x) ^ (n i) := by
  have hne : ∀ (i : Fin k) (y : BohrHull f), bohrHullChar f (b i) y ≠ 0 := by
    intro i y hzero
    have h1 := norm_bohrHullChar (hb i) y
    rw [hzero, norm_zero] at h1
    norm_num at h1
  have hcont1 : Continuous (fun y : BohrHull f => bohrHullChar f (∑ i, (n i : ℝ) * b i) y) :=
    continuous_bohrHullChar f _
  have hcont2 : Continuous (fun y : BohrHull f => ∏ i, (bohrHullChar f (b i) y) ^ (n i)) := by
    refine continuous_finsetProd _ fun i _ => ?_
    exact (continuous_bohrHullChar f (b i)).zpow₀ (n i) fun y => Or.inl (hne i y)
  have hline : ∀ t : ℝ,
      bohrHullChar f (∑ i, (n i : ℝ) * b i) (bohrIota f t)
        = ∏ i, (bohrHullChar f (b i) (bohrIota f t)) ^ (n i) := by
    intro t
    rw [bohrHullChar_bohrIota (isBohrHullFrequency_intCombination hb n) t]
    have hval : ∀ i, bohrHullChar f (b i) (bohrIota f t) = expChar (b i) t := fun i =>
      bohrHullChar_bohrIota (hb i) t
    simp only [hval]
    exact char_intCombination (fun a c => expChar_add_frequency a c t) (fun a => norm_expChar a t) b n
  exact congrFun (Continuous.ext_on (denseRange_bohrIota f) hcont1 hcont2
    (fun y hy => by obtain ⟨t, rfl⟩ := hy; exact hline t)) x

end Hull

end GaloisForLFunctions
