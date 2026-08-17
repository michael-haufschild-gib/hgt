import GaloisForLFunctions.HTGeometry.CubicPhaseEvaluationUniformity

/-!
# Eighth roots have the continuous moments in the low range

The average of a character of the additive group of residues modulo eight vanishes unless the
character is trivial: this is the geometric sum of a root of unity.  Multiplying characters over
independent coordinates therefore gives the same answer as independent continuous phases, for every
exponent vector whose entries are nonzero only through their residues.

A uniformly distributed evaluation vector -- the fifteen-wise uniformity of cubic phases -- can be
averaged coordinate by coordinate, so a monomial of net phase power below eight in every coordinate
has exactly the continuous-phase expectation.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The additive character of the residues modulo eight -/

/-- A primitive eighth root of unity. -/
def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

theorem isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8, mul_comm, mul_assoc, mul_left_comm] using h

/-- The additive character of `ZMod 8` attached to the eighth root. -/
def charEight (x : ZMod 8) : ℂ := zeta8 ^ x.val

theorem charEight_eq_one_iff {d : ZMod 8} : charEight d = 1 ↔ d = 0 := by
  constructor
  · intro h
    have hdvd := (isPrimitiveRoot_zeta8.pow_eq_one_iff_dvd d.val).mp h
    have : (d.val : ZMod 8) = 0 := by
      exact (ZMod.natCast_eq_zero_iff d.val 8).mpr hdvd
    rwa [ZMod.natCast_val, ZMod.cast_id] at this
  · intro h
    rw [h, charEight]
    norm_num

/-- **The character sum.**  Summing an additive character over all residues gives eight for the
trivial character and zero otherwise. -/
theorem sum_charEight_mul (d : ZMod 8) :
    ∑ x : ZMod 8, charEight (d * x) = if d = 0 then 8 else 0 := by
  classical
  have hmodpow : ∀ m : ℕ, zeta8 ^ (m % 8) = zeta8 ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 8]
    rw [pow_add, pow_mul, isPrimitiveRoot_zeta8.pow_eq_one, one_pow, one_mul]
  have hpow : ∀ x : ZMod 8, charEight (d * x) = (charEight d) ^ x.val := by
    intro x
    have hmod : (d * x).val = (d.val * x.val) % 8 := ZMod.val_mul d x
    rw [charEight, charEight, ← pow_mul, hmod, hmodpow]
  rw [Finset.sum_congr rfl fun x _ => hpow x]
  by_cases hd : d = 0
  · rw [if_pos hd, hd]
    have hone : charEight (0 : ZMod 8) = 1 := charEight_eq_one_iff.mpr rfl
    rw [Finset.sum_congr rfl fun x _ => by rw [hone, one_pow]]
    simp
  · rw [if_neg hd]
    have hne : charEight d ≠ 1 := fun h => hd (charEight_eq_one_iff.mp h)
    have hval : ∑ x : ZMod 8, (charEight d) ^ x.val = ∑ i ∈ Finset.range 8, (charEight d) ^ i := by
      rw [← Fin.sum_univ_eq_sum_range fun i => (charEight d) ^ (i : ℕ)]
      rfl
    rw [hval, geom_sum_eq hne]
    have h8 : (charEight d) ^ (8 : ℕ) = 1 := by
      rw [charEight, ← pow_mul, mul_comm, pow_mul, isPrimitiveRoot_zeta8.pow_eq_one, one_pow]
    rw [h8, sub_self, zero_div]

/-! ## Monomials over independent coordinates -/

variable {k : ℕ}

/-- **The monomial average factorizes.**  Over the full residue cube, a product of characters is the
product of the individual character sums. -/
theorem sum_prod_charEight (d : Fin k → ZMod 8) :
    ∑ w : Fin k → ZMod 8, ∏ a, charEight (d a * w a)
      = ∏ a, (if d a = 0 then (8 : ℂ) else 0) := by
  classical
  calc ∑ w : Fin k → ZMod 8, ∏ a, charEight (d a * w a)
      = ∑ w ∈ Fintype.piFinset (fun _ => (Finset.univ : Finset (ZMod 8))),
          ∏ a, charEight (d a * w a) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ a, ∑ y : ZMod 8, charEight (d a * y) :=
        (Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (ZMod 8)))
          (fun a y => charEight (d a * y))).symm
    _ = ∏ a, (if d a = 0 then (8 : ℂ) else 0) :=
        Finset.prod_congr rfl fun a _ => sum_charEight_mul (d a)

/-- **The low-range moment.**  A nontrivial exponent vector has vanishing monomial average, and the
trivial one has average `8^k`; this is exactly the continuous-phase answer. -/
theorem sum_prod_charEight_eq_zero {d : Fin k → ZMod 8} (hd : ∃ a, d a ≠ 0) :
    ∑ w : Fin k → ZMod 8, ∏ a, charEight (d a * w a) = 0 := by
  classical
  obtain ⟨a, ha⟩ := hd
  rw [sum_prod_charEight]
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  rw [if_neg ha]

/-! ## Transfer to a uniformly distributed ensemble -/

section Transfer

variable {Ω : Type*} [Fintype Ω]

/-- Equal fibre cardinalities follow from the uniformity identity. -/
theorem card_fiber_const_of_mul_eq (ev : Ω → (Fin k → ZMod 8))
    (h : ∀ w, ((Finset.univ.filter fun x => ev x = w).card) * 8 ^ k = Fintype.card Ω)
    (w w' : Fin k → ZMod 8) :
    (Finset.univ.filter fun x => ev x = w).card
      = (Finset.univ.filter fun x => ev x = w').card := by
  classical
  have h1 := h w
  have h2 := h w'
  have hpos : 0 < 8 ^ k := pow_pos (by norm_num) k
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

/-- **Averaging over a uniform ensemble is averaging over the cube.**  If every value has the same
number of preimages, an observable of the evaluation has ensemble sum the fibre size times the cube
sum. -/
theorem sum_comp_of_uniform (ev : Ω → (Fin k → ZMod 8)) (c : ℕ)
    (huniform : ∀ w, (Finset.univ.filter fun x => ev x = w).card = c)
    (F : (Fin k → ZMod 8) → ℂ) :
    ∑ h : Ω, F (ev h) = (c : ℂ) * ∑ w, F w := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (f := fun h : Ω => F (ev h)) (g := ev) (s := (Finset.univ : Finset Ω))
    (t := (Finset.univ : Finset (Fin k → ZMod 8))) (fun h _ => Finset.mem_univ (ev h))
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hval : ∀ h ∈ Finset.univ.filter fun x => ev x = w, F (ev h) = F w := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rw [hh.2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, huniform w, nsmul_eq_mul]

/-- **The moment transfer.**  A nontrivial monomial has vanishing ensemble average, exactly as under
independent continuous phases. -/
theorem sum_comp_prod_charEight_eq_zero (ev : Ω → (Fin k → ZMod 8)) (c : ℕ)
    (huniform : ∀ w, (Finset.univ.filter fun x => ev x = w).card = c)
    {d : Fin k → ZMod 8} (hd : ∃ a, d a ≠ 0) :
    ∑ h : Ω, ∏ a, charEight (d a * (ev h) a) = 0 := by
  classical
  rw [sum_comp_of_uniform ev c huniform (fun w => ∏ a, charEight (d a * w a)),
    sum_prod_charEight_eq_zero hd, mul_zero]

end Transfer

end

end GaloisForLFunctions.HTGeometry
