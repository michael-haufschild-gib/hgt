import GaloisForLFunctions.RHTower.Deninger.DeningerSuspendedAlternating

/-!
# Concatenation on the suspended source

Concatenating two suspended words multiplies their letter-height products and adds their letter
counts, so the two-parameter weight is *exactly multiplicative* on concatenation.  Ancestral length
and total arithmetic character are additive.

Consequently the unreduced product series of two elements of the source converges, with total mass
the product of the two masses: exterior multiplication is continuous, with no seminorm loss.

* `deningerSuspConcat` : concatenation of suspended words.
* `deningerSuspWeightR_concat` : **the weight is multiplicative.**
* `deningerSuspConcat_seminormR` : **the product series has mass the product of the masses.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Concatenation of suspended words. -/
def deningerSuspConcat (u v : DeningerSuspWord) : DeningerSuspWord :=
  ⟨u.1 + v.1, Fin.append u.2 v.2⟩

@[simp]
theorem deningerSuspConcat_length (u v : DeningerSuspWord) :
    deningerSuspWordLength (deningerSuspConcat u v)
      = deningerSuspWordLength u + deningerSuspWordLength v := rfl

theorem deningerSuspConcat_height (u v : DeningerSuspWord) :
    deningerSuspWordHeight (deningerSuspConcat u v)
      = deningerSuspWordHeight u * deningerSuspWordHeight v := by
  obtain ⟨r, f⟩ := u
  obtain ⟨s, g⟩ := v
  show (∏ i : Fin (r + s), deningerSuspHeight (Fin.append f g i)) = _
  rw [Fin.prod_univ_add]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
    (Finset.prod_congr rfl fun i _ => ?_)
  · rw [Fin.append_left]
  · rw [Fin.append_right]

theorem deningerSuspConcat_char (u v : DeningerSuspWord) :
    deningerSuspWordChar (deningerSuspConcat u v)
      = deningerSuspWordChar u + deningerSuspWordChar v := by
  obtain ⟨r, f⟩ := u
  obtain ⟨s, g⟩ := v
  show (∑ i : Fin (r + s), deningerSuspChar (Fin.append f g i)) = _
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · rw [Fin.append_left]
  · rw [Fin.append_right]

theorem deningerSuspConcat_ancestral (u v : DeningerSuspWord) :
    deningerSuspWordAncestral (deningerSuspConcat u v)
      = deningerSuspWordAncestral u + deningerSuspWordAncestral v := by
  obtain ⟨r, f⟩ := u
  obtain ⟨s, g⟩ := v
  show (∑ i : Fin (r + s), deningerSuspAncestral (Fin.append f g i)) = _
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · rw [Fin.append_left]
  · rw [Fin.append_right]

/-- **The two-parameter weight is multiplicative on concatenation.** -/
theorem deningerSuspWeightR_concat (k : ℕ) (R : ℝ) (u v : DeningerSuspWord) :
    deningerSuspWeightR k R (deningerSuspConcat u v)
      = deningerSuspWeightR k R u * deningerSuspWeightR k R v := by
  rw [deningerSuspWeightR, deningerSuspWeightR, deningerSuspWeightR,
    deningerSuspConcat_height, deningerSuspConcat_length, pow_add, mul_pow]
  ring

/-- **Exterior multiplication is continuous with no seminorm loss.**  The unreduced product series
of two elements of the suspended source converges, and its total mass is exactly the product of the
two masses. -/
theorem deningerSuspConcat_seminormR {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (a b : DeningerSuspKothe) :
    (Summable fun q : DeningerSuspWord × DeningerSuspWord =>
        deningerSuspWeightR k R (deningerSuspConcat q.1 q.2) *
          (‖(a : DeningerSuspWord → ℂ) q.1‖ * ‖(b : DeningerSuspWord → ℂ) q.2‖)) ∧
      (∑' q : DeningerSuspWord × DeningerSuspWord,
          deningerSuspWeightR k R (deningerSuspConcat q.1 q.2) *
            (‖(a : DeningerSuspWord → ℂ) q.1‖ * ‖(b : DeningerSuspWord → ℂ) q.2‖))
        = deningerSuspSeminormR k R a * deningerSuspSeminormR k R b := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hnnA : ∀ u : DeningerSuspWord,
      0 ≤ deningerSuspWeightR k R u * ‖(a : DeningerSuspWord → ℂ) u‖ := fun u =>
    mul_nonneg (deningerSuspWeightR_nonneg k hRpos.le u) (norm_nonneg _)
  have hnnB : ∀ v : DeningerSuspWord,
      0 ≤ deningerSuspWeightR k R v * ‖(b : DeningerSuspWord → ℂ) v‖ := fun v =>
    mul_nonneg (deningerSuspWeightR_nonneg k hRpos.le v) (norm_nonneg _)
  have hA := deningerSuspSeminormR_summable (k := k) hR a
  have hB := deningerSuspSeminormR_summable (k := k) hR b
  have hprod : Summable fun q : DeningerSuspWord × DeningerSuspWord =>
      (deningerSuspWeightR k R q.1 * ‖(a : DeningerSuspWord → ℂ) q.1‖) *
        (deningerSuspWeightR k R q.2 * ‖(b : DeningerSuspWord → ℂ) q.2‖) :=
    Summable.mul_of_nonneg
      (f := fun u => deningerSuspWeightR k R u * ‖(a : DeningerSuspWord → ℂ) u‖)
      (g := fun v => deningerSuspWeightR k R v * ‖(b : DeningerSuspWord → ℂ) v‖)
      hA hB hnnA hnnB
  have hterm : ∀ q : DeningerSuspWord × DeningerSuspWord,
      deningerSuspWeightR k R (deningerSuspConcat q.1 q.2) *
          (‖(a : DeningerSuspWord → ℂ) q.1‖ * ‖(b : DeningerSuspWord → ℂ) q.2‖)
        = (deningerSuspWeightR k R q.1 * ‖(a : DeningerSuspWord → ℂ) q.1‖) *
          (deningerSuspWeightR k R q.2 * ‖(b : DeningerSuspWord → ℂ) q.2‖) := by
    intro q
    rw [deningerSuspWeightR_concat]
    ring
  refine ⟨hprod.congr fun q => (hterm q).symm, ?_⟩
  rw [tsum_congr hterm]
  have hnormA : Summable fun u => ‖deningerSuspWeightR k R u *
      ‖(a : DeningerSuspWord → ℂ) u‖‖ := by
    refine hA.congr fun u => ?_
    rw [Real.norm_of_nonneg (hnnA u)]
  have hnormB : Summable fun v => ‖deningerSuspWeightR k R v *
      ‖(b : DeningerSuspWord → ℂ) v‖‖ := by
    refine hB.congr fun v => ?_
    rw [Real.norm_of_nonneg (hnnB v)]
  rw [← tsum_mul_tsum_of_summable_norm hnormA hnormB]
  rfl

end

end RHTower
