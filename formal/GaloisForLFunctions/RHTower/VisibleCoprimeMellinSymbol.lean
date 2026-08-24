import GaloisForLFunctions.RHTower.VisibleCoprimeMobiusLaplaceAddition
import GaloisForLFunctions.RHTower.DeningerPoissonMellin
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicStateFactorization
import GaloisForLFunctions.Core

/-!
# Primitive visible-lattice Mellin symbol

This leaf proves the classical absolutely convergent identity

`∑' (a,b)=1, a⁻ˢ b⁻ᵗ = ζ(s) ζ(t) / ζ(s+t)`

for `1 < re s` and `1 < re t`.  The proof uses the already formalized unique decomposition of a
positive lattice point into a coprime direction and its common gcd scale.  The product and quotient
forms are both exposed, with every reindexing justified by absolute summability.
-/

open Complex Real GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Positive-integer Dirichlet atom `n⁻ˢ`. -/
def positiveDirichletTerm (s : ℂ) (n : ℕ+) : ℂ :=
  ((n : ℕ) : ℂ) ^ (-s)

/-- Dirichlet atom attached to one positive coprime direction. -/
def visibleCoprimeMellinTerm
    (s t : ℂ) (q : ThetaCuspPrimitiveDirection) : ℂ :=
  positiveDirichletTerm s q.1.1 * positiveDirichletTerm t q.1.2

/-- Primitive two-variable visible-lattice Mellin symbol. -/
def visibleCoprimeMellinSymbol (s t : ℂ) : ℂ :=
  ∑' q : ThetaCuspPrimitiveDirection, visibleCoprimeMellinTerm s t q

/-- Positive Dirichlet atoms are absolutely summable in the Euler half-plane. -/
theorem summable_positiveDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (positiveDirichletTerm s) := by
  apply Summable.of_norm
  apply (summable_pnat_rpow hs).congr
  intro n
  rw [positiveDirichletTerm]
  simpa using (norm_cpow_neg_eq_rpow_re (n : ℝ)
    (by exact_mod_cast n.property) s).symm

/-- Positive-integer indexing gives the standard zeta Dirichlet series. -/
theorem tsum_positiveDirichletTerm_eq_riemannZeta
    (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ+, positiveDirichletTerm s n) = riemannZeta s := by
  calc
    (∑' n : ℕ+, positiveDirichletTerm s n) =
        ∑' n : ℕ, (((n : ℂ) + 1)) ^ (-s) := by
      simp_rw [positiveDirichletTerm]
      calc
        (∑' n : ℕ+, ((n : ℕ) : ℂ) ^ (-s)) =
            ∑' n : ℕ, (((n + 1 : ℕ) : ℂ)) ^ (-s) :=
          tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ (-s))
        _ = ∑' n : ℕ, (((n : ℂ) + 1)) ^ (-s) := by
          apply tsum_congr
          intro n
          apply congrArg (fun z : ℂ => z ^ (-s))
          norm_num
    _ = riemannZeta s := tsum_one_add_cpow_eq_zeta hs

private theorem summable_positiveDirichletPair
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    Summable (fun p : ℕ+ × ℕ+ =>
      positiveDirichletTerm s p.1 * positiveDirichletTerm t p.2) := by
  have hss := summable_positiveDirichletTerm hs
  have htt := summable_positiveDirichletTerm ht
  apply Summable.of_norm
  simpa only [norm_mul] using
    hss.norm.mul_of_nonneg htt.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- The primitive coprime Mellin family is absolutely summable. -/
theorem summable_visibleCoprimeMellinTerm
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    Summable (visibleCoprimeMellinTerm s t) := by
  exact (summable_positiveDirichletPair s t hs ht).comp_injective Subtype.val_injective

private theorem visibleCoprimeMellin_ray_factor
    (s t : ℂ) (q : ThetaCuspPrimitiveDirection) (d : ℕ+) :
    visibleCoprimeMellinTerm s t q * positiveDirichletTerm (s + t) d =
      positiveDirichletTerm s (q.1.1 * d) *
        positiveDirichletTerm t (q.1.2 * d) := by
  have ha : (0 : ℝ) ≤ (q.1.1 : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (q.1.2 : ℝ) := by positivity
  have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hdne : (((d : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by exact_mod_cast d.ne_zero)
  unfold visibleCoprimeMellinTerm positiveDirichletTerm
  change (((q.1.1 : ℝ) : ℂ) ^ (-s)) * (((q.1.2 : ℝ) : ℂ) ^ (-t)) *
      (((d : ℝ) : ℂ) ^ (-(s + t))) =
    ((((q.1.1 * d : ℕ+) : ℝ) : ℂ) ^ (-s)) *
      ((((q.1.2 * d : ℕ+) : ℝ) : ℂ) ^ (-t))
  have hcastA : (((q.1.1 * d : ℕ+) : ℝ) : ℂ) =
      ((q.1.1 : ℝ) : ℂ) * ((d : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcastB : (((q.1.2 * d : ℕ+) : ℝ) : ℂ) =
      ((q.1.2 : ℝ) : ℂ) * ((d : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowd : (((d : ℝ) : ℂ) ^ (-s)) * (((d : ℝ) : ℂ) ^ (-t)) =
      ((d : ℝ) : ℂ) ^ (-(s + t)) := by
    rw [← Complex.cpow_add _ _ hdne]
    congr 1
    ring
  rw [hcastA, hcastB,
    Complex.mul_cpow_ofReal_nonneg ha hd,
    Complex.mul_cpow_ofReal_nonneg hb hd, ← hpowd]
  ring

/-- Denominator-free primitive Mellin identity. -/
theorem visibleCoprimeMellinSymbol_mul_riemannZeta
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    visibleCoprimeMellinSymbol s t * riemannZeta (s + t) =
      riemannZeta s * riemannZeta t := by
  let f : ℕ+ × ℕ+ → ℂ := fun p =>
    positiveDirichletTerm s p.1 * positiveDirichletTerm t p.2
  have hfull : Summable f := summable_positiveDirichletPair s t hs ht
  have hray : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      f (thetaCuspPrimitiveRayIndexToPositivePair q)) :=
    (Equiv.summable_iff thetaCuspPrimitiveRayIndexEquivPositivePair).2 hfull
  have hst : 1 < (s + t).re := by
    simp only [add_re]
    linarith
  have hdir := summable_visibleCoprimeMellinTerm s t hs ht
  have hd := summable_positiveDirichletTerm hst
  have hprod : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      visibleCoprimeMellinTerm s t q.1 * positiveDirichletTerm (s + t) q.2) := by
    apply hray.congr
    rintro ⟨q, d⟩
    exact (visibleCoprimeMellin_ray_factor s t q d).symm
  calc
    visibleCoprimeMellinSymbol s t * riemannZeta (s + t) =
        (∑' q : ThetaCuspPrimitiveDirection, visibleCoprimeMellinTerm s t q) *
          (∑' d : ℕ+, positiveDirichletTerm (s + t) d) := by
      rw [visibleCoprimeMellinSymbol,
        tsum_positiveDirichletTerm_eq_riemannZeta (s + t) hst]
    _ = ∑' q : ThetaCuspPrimitiveRayIndex,
          visibleCoprimeMellinTerm s t q.1 * positiveDirichletTerm (s + t) q.2 :=
      hdir.tsum_mul_tsum hd hprod
    _ = ∑' q : ThetaCuspPrimitiveRayIndex,
          f (thetaCuspPrimitiveRayIndexToPositivePair q) := by
      apply tsum_congr
      rintro ⟨q, d⟩
      exact visibleCoprimeMellin_ray_factor s t q d
    _ = ∑' p : ℕ+ × ℕ+, f p :=
      (tsum_thetaCuspPositivePair_eq_primitiveRay f).symm
    _ = (∑' a : ℕ+, positiveDirichletTerm s a) *
          (∑' b : ℕ+, positiveDirichletTerm t b) := by
      exact (summable_positiveDirichletTerm hs).tsum_mul_tsum
        (summable_positiveDirichletTerm ht) hfull |>.symm
    _ = riemannZeta s * riemannZeta t := by
      rw [tsum_positiveDirichletTerm_eq_riemannZeta s hs,
        tsum_positiveDirichletTerm_eq_riemannZeta t ht]

/-- Classical primitive-lattice zeta quotient `(V6)`. -/
theorem visibleCoprimeMellinSymbol_eq_zeta_quotient
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    visibleCoprimeMellinSymbol s t =
      riemannZeta s * riemannZeta t / riemannZeta (s + t) := by
  have hst : 1 ≤ (s + t).re := by
    simp only [add_re]
    linarith
  have hnz : riemannZeta (s + t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hst
  apply (mul_right_cancel₀ hnz)
  rw [visibleCoprimeMellinSymbol_mul_riemannZeta s t hs ht]
  field_simp

end

end RHTower
