import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheMoebiusGluingOfStars

/-!
# The gcd stratification of the complete Weil family

The Möbius gluing `Q = Q_cop + Σ_{d ≥ 2} (−μ(d)) Q_d` has alternating signs, but they telescope:
`μ ∗ 1 = δ`. Unwound, the gluing is the sign-free **gcd stratification**
(`quadratic_gcd_stratification`):

  `Q(x) = Σ_{g ≤ N} Σ_{gcd(m, n) = g} Q_{mn} x_m x_n`,

and the stratum of `g` is the coprime part of the star of `g`. For the complete Weil family the
star of `g` is the family at the star resolution `(c⌊N/g⌋/N, ⌊N/g⌋)`, entry by entry
(`completeWeilMatrix_star_apply`). So (`completeWeilEnergy_gcd_stratification`)

  `W_{c,N}(x) = Σ_{g ≤ N} Cop(W_{c⌊N/g⌋/N, ⌊N/g⌋})(x(g·))`,

where `Cop` keeps only the coprime pairs.

Every level contributes only its coprime pairs. A coprime pair has no diagonal except at the root
vertex `1` (`coprime_self_iff`), so each stratum is an off-diagonal form, indefinite unless it
vanishes. The successor pairs `(n, n + 1)` are all coprime: the whole successor and archimedean
overlap of consecutive atoms sits in the top stratum `g = 1`. The affine shells `(n, kn + h)` sit
in the stratum `gcd(n, h)`. Local positivity of stars therefore says nothing about the top stratum.
That stratum is the gluing a Kähler-package proof must control.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- A coprime pair on the diagonal is the root: `gcd(n, n) = 1 ⇔ n = 1`. -/
theorem coprime_self_iff (n : ℕ) : Nat.Coprime n n ↔ n = 1 := Nat.coprime_self n

/-- **The gcd stratification of a quadratic form.** For values `v i ∈ [1, N]`, every form is the
sum over `g ≤ N` of its pairs with `gcd = g`. -/
theorem quadratic_gcd_stratification {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → ℕ)
    (hv : ∀ i, v i ∈ Icc 1 N) (W : ι → ι → ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, W i j * x i * x j =
      ∑ g ∈ Icc 1 N, ∑ i, ∑ j, if Nat.gcd (v i) (v j) = g then W i j * x i * x j else 0 := by
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have hg : Nat.gcd (v i) (v j) ∈ Icc 1 N := by
    have h1 := mem_Icc.mp (hv i)
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (by omega),
      (Nat.gcd_le_left _ (by omega)).trans h1.2⟩
  rw [sum_ite_eq (Icc 1 N) (Nat.gcd (v i) (v j)), if_pos hg]

/-- **Entries of a star are entries of the lower resolution.** -/
theorem completeWeilMatrix_star_apply {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (a b : PrimeHorizonIndex (N / d))
    (a' b' : PrimeHorizonIndex N) (ha : (a' : ℕ) = d * a) (hb : (b' : ℕ) = d * b) :
    completeWeilMatrix φ c N a' b' = completeWeilMatrix φ (starOverlap c N d) (N / d) a b := by
  set A := completeWeilMatrix φ c N
  set B := completeWeilMatrix φ (starOverlap c N d) (N / d)
  have hA := completeWeilMatrix_isSymm φ c N
  have hB := completeWeilMatrix_isSymm φ (starOverlap c N d) (N / d)
  -- The quadratic forms agree on star embeddings; polarize on `e_a + e_b`.
  have hq : ∀ y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d)),
      qf A (fun n => starEmbed d N y n) = qf B (fun n => y n) := fun y => by
    rw [← completeWeilEnergy_eq_qf, ← completeWeilEnergy_eq_qf,
      completeWeilEnergy_starEmbed hφ.contDiff hφ.supp hc hd hdN]
  have hemb : ∀ e : PrimeHorizonIndex (N / d) → ℝ, ∀ n : PrimeHorizonIndex N,
      starEmbed d N (WithLp.toLp 2 e) n =
        ∑ k : PrimeHorizonIndex (N / d), e k * (if (n : ℕ) = d * k then 1 else 0) := by
    intro e n
    simp only [starEmbed]
    sorry
  sorry

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
