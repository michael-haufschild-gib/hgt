import GaloisForLFunctions.RHTower.DirichletCharacterOrthogonality
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMoment
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# The mean value theorem for Dirichlet character sums

For a modulus `q = n + 1` and coefficients `a : ℕ → ℂ`, orthogonality of the character family
diagonalises the family second moment of `charSum n N a χ = ∑_{k ≤ N} a k χ(k)` into the reduced
residue classes:

```
∑_{χ mod q} ‖∑_{k ≤ N} a k χ(k)‖² = φ(q) · ∑_{u ∈ (ZMod q)ˣ} ‖∑_{k ≤ N, k ≡ u} a k‖² .
```

Bounding each class sum by Cauchy's inequality and the interval occupancy `N/q + 1` of a residue
class gives the mean value theorem, `meanValue_charSum`:

```
∑_{χ mod q} ‖∑_{k ≤ N} a k χ(k)‖² ≤ φ(q) · (N/q + 1) · ∑_{k ≤ N, (k,q) = 1} ‖a k‖² .
```

The class-occupancy Cauchy step is the corpus lemma `sum_residueClassL1Mass_sq_le`.
-/

open Finset

noncomputable section

namespace RHTower

/-- The Dirichlet character sum `∑_{k ≤ N} a k · χ(k)`. -/
def charSum (n N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ (n + 1)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, a k * χ (k : ZMod (n + 1))

/-- The sum of the coefficients over one reduced residue class. -/
def classSum (n N : ℕ) (a : ℕ → ℂ) (u : (ZMod (n + 1))ˣ) : ℂ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))), a k

theorem conj_char (n : ℕ) (χ : DirichletCharacter ℂ (n + 1)) (v : (ZMod (n + 1))ˣ) :
    (starRingEnd ℂ) (χ (v : ZMod (n + 1))) = χ ((v : ZMod (n + 1))⁻¹) := by
  have hne : χ (v : ZMod (n + 1)) ≠ 0 := by
    intro h
    have h1 : χ ((v : ZMod (n + 1))⁻¹) * χ (v : ZMod (n + 1)) = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit _ v.isUnit, map_one]
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have h1 : χ ((v : ZMod (n + 1))⁻¹) * χ (v : ZMod (n + 1)) = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit _ v.isUnit, map_one]
  have h2 : (starRingEnd ℂ) (χ (v : ZMod (n + 1))) = (χ (v : ZMod (n + 1)))⁻¹ := by
    have := MulChar.star_apply' χ (v : ZMod (n + 1))
    rw [MulChar.inv_apply_eq_inv'] at this
    simpa using this
  rw [h2, eq_comm]
  exact eq_inv_of_mul_eq_one_left h1

/-- Summing a function over the reduced residue classes recovers its sum over the
integers coprime to the modulus. -/
theorem sum_over_units_fibers (n N : ℕ) (F : ℕ → ℂ) :
    ∑ u : (ZMod (n + 1))ˣ,
        ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))), F k
      = ∑ k ∈ Finset.Icc 1 N, (if IsUnit (Nat.cast k : ZMod (n + 1)) then F k else 0) := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : IsUnit (Nat.cast k : ZMod (n + 1))
  · rw [if_pos hk]
    have hsingle : ∀ u ∈ (Finset.univ : Finset (ZMod (n + 1))ˣ), u ≠ hk.unit →
        (if (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1)) then F k else 0) = 0 := by
      intro u _ hune
      have hne : (Nat.cast k : ZMod (n + 1)) ≠ (u : ZMod (n + 1)) := by
        intro heq
        apply hune
        apply Units.ext
        rw [← heq, IsUnit.unit_spec]
      simp [hne]
    have hmem : hk.unit ∉ (Finset.univ : Finset (ZMod (n + 1))ˣ) →
        (if (Nat.cast k : ZMod (n + 1)) = ((hk.unit : (ZMod (n + 1))ˣ) : ZMod (n + 1))
          then F k else 0) = 0 := fun h => absurd (Finset.mem_univ _) h
    rw [Finset.sum_eq_single hk.unit hsingle hmem]
    rw [IsUnit.unit_spec]
    simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun u _ => ?_)
    have hne : (Nat.cast k : ZMod (n + 1)) ≠ (u : ZMod (n + 1)) := by
      intro heq
      exact hk (heq ▸ u.isUnit)
    simp [hne]

/-- The character sum splits over the reduced residue classes. -/
theorem charSum_eq_sum_classSum (n N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ (n + 1)) :
    charSum n N a χ = ∑ u : (ZMod (n + 1))ˣ, classSum n N a u * χ (u : ZMod (n + 1)) := by
  classical
  have hrhs : ∀ u : (ZMod (n + 1))ˣ,
      classSum n N a u * χ (u : ZMod (n + 1))
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))),
            a k * χ (k : ZMod (n + 1)) := by
    intro u
    rw [classSum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [(Finset.mem_filter.1 hk).2]
  simp only [hrhs]
  rw [sum_over_units_fibers, charSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : IsUnit (Nat.cast k : ZMod (n + 1))
  · rw [if_pos hk]
  · rw [if_neg hk, MulChar.map_nonunit χ hk, mul_zero]


/-- **Exact second moment of a character sum.**  Orthogonality diagonalises the family sum into
the reduced residue classes. -/
theorem sum_normSq_charSum (n N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ (n + 1), ‖charSum n N a χ‖ ^ 2
      = ((n + 1).totient : ℝ) * ∑ u : (ZMod (n + 1))ˣ, ‖classSum n N a u‖ ^ 2 := by
  classical
  have hbil := dirichletCharacterFamily_bilinear n (classSum n N a)
    (fun v => (starRingEnd ℂ) (classSum n N a v))
  have hleft : ∀ χ : DirichletCharacter ℂ (n + 1),
      (∑ u, classSum n N a u * χ (u : ZMod (n + 1)))
        * (∑ v, (starRingEnd ℂ) (classSum n N a v) * χ ((v : ZMod (n + 1))⁻¹))
      = (‖charSum n N a χ‖ ^ 2 : ℝ) := by
    intro χ
    have h1 : ∑ u, classSum n N a u * χ (u : ZMod (n + 1)) = charSum n N a χ :=
      (charSum_eq_sum_classSum n N a χ).symm
    have h2 : ∑ v, (starRingEnd ℂ) (classSum n N a v) * χ ((v : ZMod (n + 1))⁻¹)
        = (starRingEnd ℂ) (charSum n N a χ) := by
      rw [charSum_eq_sum_classSum n N a χ, map_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [map_mul, conj_char n χ v]
    rw [h1, h2, Complex.mul_conj']
    norm_cast
  rw [Finset.sum_congr rfl (fun χ _ => hleft χ)] at hbil
  have hright : ∑ u, classSum n N a u * (starRingEnd ℂ) (classSum n N a u)
      = ((∑ u : (ZMod (n + 1))ˣ, ‖classSum n N a u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Complex.mul_conj']
  rw [hright] at hbil
  have : ((∑ χ : DirichletCharacter ℂ (n + 1), ‖charSum n N a χ‖ ^ 2 : ℝ) : ℂ)
      = (((n + 1).totient : ℝ) * ∑ u : (ZMod (n + 1))ˣ, ‖classSum n N a u‖ ^ 2 : ℝ) := by
    push_cast
    push_cast at hbil
    exact hbil
  exact_mod_cast this


/-- The reduced-class filter is the residue filter. -/
theorem classFilter_eq (n N : ℕ) (u : (ZMod (n + 1))ˣ) :
    (Finset.Icc 1 N).filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1)))
      = (Finset.Icc 1 N).filter (fun k : ℕ => k % (n + 1) = ((u : ZMod (n + 1)).val)) := by
  classical
  refine Finset.filter_congr (fun k _ => ?_)
  constructor
  · intro h
    rw [← ZMod.val_natCast, h]
  · intro h
    have : (Nat.cast k : ZMod (n + 1)).val = ((u : ZMod (n + 1))).val := by
      rw [ZMod.val_natCast]; exact h
    exact ZMod.val_injective _ this

/-- **Mean value theorem for Dirichlet character sums.**  (Matomäki--Teräväinen, Lemma 3.7.) -/
theorem meanValue_charSum (n N : ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ (n + 1), ‖charSum n N a χ‖ ^ 2
      ≤ ((n + 1).totient : ℝ) * (((N : ℝ) / ((n + 1 : ℕ) : ℝ) + 1)
          * ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
              ‖a k‖ ^ 2) := by
  classical
  set b : ℕ → ℂ := fun k => if IsUnit (Nat.cast k : ZMod (n + 1)) then a k else 0 with hbdef
  have hstep : ∀ u : (ZMod (n + 1))ˣ,
      ‖classSum n N a u‖ ≤ residueClassL1Mass n N ((u : ZMod (n + 1)).val) b := by
    intro u
    rw [classSum, classFilter_eq, residueClassL1Mass]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hu : (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1)) := by
      have := (Finset.mem_filter.1 hk).2
      have hv : (Nat.cast k : ZMod (n + 1)).val = ((u : ZMod (n + 1))).val := by
        rw [ZMod.val_natCast]; exact this
      exact ZMod.val_injective _ hv
    have : b k = a k := by rw [hbdef]; simp [hu, u.isUnit]
    rw [this]
  have hinj : Function.Injective (fun u : (ZMod (n + 1))ˣ => ((u : ZMod (n + 1)).val)) := by
    intro u v huv
    exact Units.ext (ZMod.val_injective _ huv)
  have hsum1 : ∑ u : (ZMod (n + 1))ˣ, ‖classSum n N a u‖ ^ 2
      ≤ ∑ u : (ZMod (n + 1))ˣ, residueClassL1Mass n N ((u : ZMod (n + 1)).val) b ^ 2 := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    have h0 : (0 : ℝ) ≤ ‖classSum n N a u‖ := norm_nonneg _
    nlinarith [hstep u, h0, norm_nonneg (classSum n N a u)]
  have hsum2 : ∑ u : (ZMod (n + 1))ˣ, residueClassL1Mass n N ((u : ZMod (n + 1)).val) b ^ 2
      ≤ ∑ r ∈ Finset.range (n + 1), residueClassL1Mass n N r b ^ 2 := by
    rw [← Finset.sum_image (f := fun r => residueClassL1Mass n N r b ^ 2)
      (g := fun u : (ZMod (n + 1))ˣ => ((u : ZMod (n + 1)).val))
      (s := (Finset.univ : Finset (ZMod (n + 1))ˣ)) (fun x _ y _ h => hinj h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => sq_nonneg _)
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    exact Finset.mem_range.2 (ZMod.val_lt _)
  have hsum3 : ∑ k ∈ Finset.Icc 1 N, ‖b k‖ ^ 2
      = ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
          ‖a k‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hbdef]
    by_cases h : IsUnit (Nat.cast k : ZMod (n + 1)) <;> simp [h]
  have hcorpus := sum_residueClassL1Mass_sq_le n N b
  rw [hsum3] at hcorpus
  rw [sum_normSq_charSum]
  have htot : (0 : ℝ) ≤ ((n + 1).totient : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (le_trans hsum1 (le_trans hsum2 hcorpus)) htot

end RHTower
