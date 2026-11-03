import GaloisForLFunctions.WindowTowerOfSpecZ.TheRationalLatticeOfAWindow

/-!
# The folds count multiplicative pairs

On the rational lattice the fold correlations are counts. For the indicator of a finite configuration
`S ⊂ ℚ_{>0}` of spread `< A` (all amplitudes `1`):

* **The fold correlation counts the pairs `(r, nr)` inside `S`** (`integral_ratLattice_one_eq_card`):
  `∫ι_S(u)ι_S(u + log n) du = ‖φ‖² · #{r ∈ S : nr ∈ S}`; in particular `‖ι_S‖² = ‖φ‖²·#S`.
* **The fold energy counts the cut pairs** (`foldEnergy_ratLattice_eq_card`):
  `∫(ι_S(u) − ι_S(u + log n))² = ‖φ‖² · (2#S − 2#{r ∈ S : nr ∈ S})`, the number of `n`-edges `{r, nr}`
  with exactly one end in `S`: `#{r ∈ S : nr ∉ S} + #{s ∈ S : s/n ∉ S}`.

So on configurations the symmetric fold mass `sym_n` is the number of multiplicative `n`-pairs of the
configuration and Weil's arithmetic term `Σ_n Λ(n)n^{−1/2}∫H(u)H(u + log n)` is the weighted count
`‖φ‖² Σ_n Λ(n)n^{−1/2}·#{r ∈ S : nr ∈ S}` of its multiplicative pairs.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ MeasureTheory Set

variable {A : ℝ}

/-- `Σ_{r,s∈S} [s = nr] = #{r ∈ S : nr ∈ S}`. -/
theorem sum_sum_ite_eq_card (S : Finset ℚ) (n : ℕ) :
    (∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then (1 : ℝ) * 1 else 0) =
      ((S.filter fun r => (n : ℚ) * r ∈ S).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hcast : ∀ s : ℚ, ((s : ℝ) = n * r ↔ s = n * r) := fun s => by
    constructor
    · intro h; exact_mod_cast h
    · intro h; rw [h]; push_cast; ring
  simp only [mul_one, hcast]
  rw [Finset.sum_ite_eq' S ((n : ℚ) * r) fun _ => (1 : ℝ)]
  split_ifs <;> simp

/-- **The fold correlation of a configuration counts its multiplicative pairs.** -/
theorem integral_ratLattice_one_eq_card (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) (N : ℕ) :
    ∃ (x : ℝ) (φ : ContDiffBump (0 : ℝ)), 0 < ∫ u, φ u ^ 2 ∧
      IsWindowTest A (ratLattice S x φ fun _ => 1) ∧
      ∀ n ∈ Finset.Icc 1 N, ∫ u, ratLattice S x φ (fun _ => 1) u *
          ratLattice S x φ (fun _ => 1) (u + Real.log n) =
        (∫ u, φ u ^ 2) * ((S.filter fun r => (n : ℚ) * r ∈ S).card : ℝ) := by
  obtain ⟨x, φ, hI, hH, hcorr⟩ := exists_rationalLattice S hpos hspread N
  refine ⟨x, φ, hI, hH _, fun n hn => ?_⟩
  rw [hcorr _ n hn, sum_sum_ite_eq_card]

/-- **The fold energy of a configuration counts its cut pairs**:
`∫(ι_S(u) − ι_S(u + log n))² = ‖φ‖²(2#S − 2#{r ∈ S : nr ∈ S})`. -/
theorem foldEnergy_ratLattice_eq_card (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) {N : ℕ} (hN : 1 ≤ N) :
    ∃ (x : ℝ) (φ : ContDiffBump (0 : ℝ)), 0 < ∫ u, φ u ^ 2 ∧
      IsWindowTest A (ratLattice S x φ fun _ => 1) ∧
      ∀ n ∈ Finset.Icc 1 N, ∫ u, (ratLattice S x φ (fun _ => 1) u -
          ratLattice S x φ (fun _ => 1) (u + Real.log n)) ^ 2 =
        (∫ u, φ u ^ 2) * (2 * S.card - 2 * (S.filter fun r => (n : ℚ) * r ∈ S).card) := by
  obtain ⟨x, φ, hI, hH, hcorr⟩ := integral_ratLattice_one_eq_card S hpos hspread N
  refine ⟨x, φ, hI, hH, fun n hn => ?_⟩
  set H := ratLattice S x φ fun _ => 1
  have hc := hH.continuous
  have iH : Integrable fun u => H u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq hc
    hH.hasCompactSupport
  have iH' : Integrable fun u => H (u + Real.log n) ^ 2 := iH.comp_add_right _
  have iP : Integrable fun u => H u * H (u + Real.log n) :=
    (hc.mul (hc.comp (continuous_add_const _))).integrable_of_hasCompactSupport
      hH.hasCompactSupport.mul_right
  -- the norm is the count of the configuration
  have h1 := hcorr 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
  have hfilt1 : (S.filter fun r => ((1 : ℕ) : ℚ) * r ∈ S) = S := by
    ext r; simp only [Finset.mem_filter, Nat.cast_one, one_mul, and_self]
  rw [hfilt1] at h1
  have hnorm : ∫ u, H u ^ 2 = (∫ u, φ u ^ 2) * S.card := by
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
  have hshift : ∫ u, H (u + Real.log n) ^ 2 = ∫ u, H u ^ 2 :=
    integral_add_right_eq_self (μ := volume) (fun u => H u ^ 2) _
  have hexp : ∫ u, (H u - H (u + Real.log n)) ^ 2 =
      (∫ u, H u ^ 2) + (∫ u, H (u + Real.log n) ^ 2) - 2 * ∫ u, H u * H (u + Real.log n) := by
    have iS : Integrable fun u => H u ^ 2 + H (u + Real.log n) ^ 2 := iH.add iH'
    have iP2 : Integrable fun u => 2 * (H u * H (u + Real.log n)) := iP.const_mul 2
    rw [← integral_add iH iH', ← integral_const_mul, ← integral_sub iS iP2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [hexp, hshift, hnorm, hcorr n hn]
  ring

end GaloisForLFunctions.WindowTowerOfSpecZ
