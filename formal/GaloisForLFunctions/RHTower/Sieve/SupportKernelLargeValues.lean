import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality
import GaloisForLFunctions.RHTower.Sieve.GallagherLemma
import GaloisForLFunctions.RHTower.Sieve.LowHeightPoly

/-!
# Halász–Montgomery at a finite frequency set, with the kernel as a parameter

For a Dirichlet polynomial supported on a finite set `S` of integers and a finite set `T` of
frequencies, duality bounds the discrete mean square by the Gram row of the phase family:

```text
   ∑_{w ∈ T} ‖∑_{n ∈ S} a_n n^{2πiw}‖²  ≤  (#S + E·#T) · ∑_{n ∈ S} ‖a_n‖² ,
   E := an upper bound for ‖∑_{n ∈ S} n^{2πi(u−v)}‖ over distinct u, v ∈ T .
```

The diagonal of the Gram matrix is `#S`; every off-diagonal entry is an exponential sum over `S` at
a nonzero frequency, and the whole arithmetic content of a large-values estimate is the bound `E`
for it.  With `S` a set of primes and `E` supplied by the twisted prime number theorem this is the
Halász inequality for prime-supported coefficients; the diagonal `#S = π(2P) − π(P)` is then smaller
than the length `P` of the polynomial by a factor `log P`, which is what makes the prime version
stronger than the version for all integers.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

/-- Frequencies add in the phase. -/
theorem unitLogPhase_add (u v : ℝ) (n : ℕ) :
    unitLogPhase (u + v) n = unitLogPhase u n * unitLogPhase v n := by
  rw [unitLogPhase, unitLogPhase, unitLogPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugation reverses the frequency. -/
theorem conj_unitLogPhase (w : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (unitLogPhase w n) = unitLogPhase (-w) n := by
  rw [unitLogPhase, unitLogPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The phase at frequency zero is one. -/
theorem unitLogPhase_zero (n : ℕ) : unitLogPhase 0 n = 1 := by
  rw [unitLogPhase]
  norm_num

/-- The conjugate phase vector of a frequency, indexed by a finite support. -/
def supportPhase (S : Finset ℕ) (w : ℝ) : EuclideanSpace ℂ {p // p ∈ S} :=
  WithLp.toLp 2 (fun p => unitLogPhase (-w) (p : ℕ))

/-- The coefficient vector, indexed by the same support. -/
def supportCoeff (S : Finset ℕ) (a : ℕ → ℂ) : EuclideanSpace ℂ {p // p ∈ S} :=
  WithLp.toLp 2 (fun p => a (p : ℕ))

/-- The Gram entry of the phase family is the exponential sum at the frequency difference. -/
theorem inner_supportPhase (S : Finset ℕ) (w v : ℝ) :
    ⟪supportPhase S w, supportPhase S v⟫_ℂ = ∑ p ∈ S, unitLogPhase (w - v) p := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, supportPhase, WithLp.ofLp_toLp, Finset.univ_eq_attach]
  rw [← Finset.sum_attach S (fun p => unitLogPhase (w - v) p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conj_unitLogPhase, neg_neg, ← unitLogPhase_add]
  congr 1
  ring

/-- Pairing the phase family against the coefficient vector gives the Dirichlet polynomial. -/
theorem inner_supportPhase_coeff (S : Finset ℕ) (a : ℕ → ℂ) (w : ℝ) :
    ⟪supportPhase S w, supportCoeff S a⟫_ℂ = logPoly a S w := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, supportPhase, supportCoeff, WithLp.ofLp_toLp,
    Finset.univ_eq_attach]
  rw [logPoly, ← Finset.sum_attach S
    (fun p => a p * Complex.exp (((2 * Real.pi * (w * Real.log p) : ℝ) : ℂ) * Complex.I))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conj_unitLogPhase, neg_neg]
  rfl

/-- The energy of the coefficient vector. -/
theorem norm_supportCoeff_sq (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖supportCoeff S a‖ ^ (2 : ℕ) = ∑ p ∈ S, ‖a p‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [supportCoeff, WithLp.ofLp_toLp, Finset.univ_eq_attach]
  rw [← Finset.sum_attach S (fun p => ‖a p‖ ^ (2 : ℕ))]

/-- **The Gram row.**  The diagonal contributes the cardinality of the support and every other
entry contributes at most the kernel bound. -/
theorem row_supportPhase_le {S : Finset ℕ} {T : Finset ℝ} {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ‖∑ p ∈ S, unitLogPhase (u - v) p‖ ≤ E)
    {w : ℝ} (hw : w ∈ T) :
    ∑ v ∈ T, ‖⟪supportPhase S w, supportPhase S v⟫_ℂ‖ ≤ (S.card : ℝ) + E * (T.card : ℝ) := by
  classical
  have hdiag : ‖⟪supportPhase S w, supportPhase S w⟫_ℂ‖ = (S.card : ℝ) := by
    rw [inner_supportPhase]
    have hz : ∀ p ∈ S, unitLogPhase (w - w) p = 1 := by
      intro p _
      rw [sub_self, unitLogPhase_zero]
    rw [Finset.sum_congr rfl hz]
    simp
  have hsplit : ∑ v ∈ T, ‖⟪supportPhase S w, supportPhase S v⟫_ℂ‖
      = (∑ v ∈ T.erase w, ‖⟪supportPhase S w, supportPhase S v⟫_ℂ‖)
        + ‖⟪supportPhase S w, supportPhase S w⟫_ℂ‖ :=
    (Finset.sum_erase_add T _ hw).symm
  have hoff : ∑ v ∈ T.erase w, ‖⟪supportPhase S w, supportPhase S v⟫_ℂ‖
      ≤ ((T.erase w).card : ℝ) * E := by
    have hb : ∀ v ∈ T.erase w, ‖⟪supportPhase S w, supportPhase S v⟫_ℂ‖ ≤ E := by
      intro v hv
      rw [inner_supportPhase]
      exact hE w hw v (Finset.mem_of_mem_erase hv) (Ne.symm (Finset.ne_of_mem_erase hv))
    have := Finset.sum_le_card_nsmul (T.erase w) _ E hb
    simpa [nsmul_eq_mul] using this
  have hcard : ((T.erase w).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Nat.cast_le.2 (Finset.card_le_card (Finset.erase_subset _ _))
  have hstep : ((T.erase w).card : ℝ) * E ≤ (T.card : ℝ) * E :=
    mul_le_mul_of_nonneg_right hcard hE0
  rw [hsplit, hdiag]
  linarith

/-- **Halász–Montgomery at a finite frequency set, row form.**  The discrete mean square of a
Dirichlet polynomial supported on `S` over a finite frequency set `T` is at most the largest Gram
row of the exponential-sum kernel times the coefficient energy.  This is the form a large-values
argument uses: the row sum, not the number of frequencies times the largest entry, is what a
decaying kernel controls. -/
theorem sum_normSq_logPoly_le_of_rowBound (a : ℕ → ℂ) {S : Finset ℕ} {T : Finset ℝ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ)
    (hrow : ∀ u ∈ T, ∑ v ∈ T, ‖∑ p ∈ S, unitLogPhase (u - v) p‖ ≤ Δ) :
    ∑ w ∈ T, ‖logPoly a S w‖ ^ (2 : ℕ) ≤ Δ * ∑ p ∈ S, ‖a p‖ ^ (2 : ℕ) := by
  have hrow' : ∀ u ∈ T, ∑ v ∈ T, ‖⟪supportPhase S u, supportPhase S v⟫_ℂ‖ ≤ Δ := by
    intro u hu
    refine le_trans (le_of_eq ?_) (hrow u hu)
    exact Finset.sum_congr rfl fun v _ => by rw [inner_supportPhase]
  have hmain := sum_norm_inner_sq_le_of_schur (H := EuclideanSpace ℂ {p // p ∈ S}) T
    (supportPhase S) hΔ hrow' (supportCoeff S a)
  rw [norm_supportCoeff_sq] at hmain
  refine le_trans (le_of_eq ?_) hmain
  exact Finset.sum_congr rfl fun w _ => by rw [inner_supportPhase_coeff]

/-- **Halász–Montgomery at a finite frequency set.**  The discrete mean square of a Dirichlet
polynomial supported on `S` over a finite frequency set `T` is at most `(#S + E·#T)` times the
coefficient energy, where `E` bounds the exponential sum over `S` at every nonzero frequency
difference of `T`. -/
theorem sum_normSq_logPoly_le_of_kernelBound (a : ℕ → ℂ) {S : Finset ℕ} {T : Finset ℝ} {E : ℝ}
    (hE0 : 0 ≤ E)
    (hE : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ‖∑ p ∈ S, unitLogPhase (u - v) p‖ ≤ E) :
    ∑ w ∈ T, ‖logPoly a S w‖ ^ (2 : ℕ)
      ≤ ((S.card : ℝ) + E * (T.card : ℝ)) * ∑ p ∈ S, ‖a p‖ ^ (2 : ℕ) :=
  sum_normSq_logPoly_le_of_rowBound a (by positivity)
    (fun w hw => le_trans (le_of_eq (Finset.sum_congr rfl fun v _ =>
        congrArg norm (inner_supportPhase S w v).symm)) (row_supportPhase_le hE0 hE hw))

end

end RHTower.Sieve
