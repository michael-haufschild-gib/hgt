import GaloisForLFunctions.HTGeometry.WeakStarFormationContinuity

/-!
# Poisson-dust formation compactification

Let `K` be a compact metrizable commutative monoid and `M(K) = C(K, ℂ)*` its measure algebra
(complex Radon measures, total-variation norm, convolution).  A finite positive packet
`A = (α_1, …, α_m)` has the formation `Λ_A(z) = Π_j (δ_1 + z α_j)` and mass `|A|_1 = Σ_j ‖α_j‖`
`(PDF.2)`–`(PDF.3)`; the convolution exponential `Exp_⋆(z γ)` converges in norm `(PDF.4)`.

**Theorem 4.1.**  Packets of mass `≤ C` have a subsequence whose formations converge, against every
test function and uniformly on compact `z`-sets `(PDF.5)`, to a decorated formation
`Exp_⋆(z γ) ⋆ Π_j (δ_1 + z α_j)` with positive dust `γ`, positive atoms `α_j` and
`‖γ‖ + Σ_j ‖α_j‖ ≤ C` `(PDF.11)`–`(PDF.12)`.  Order each packet by decreasing mass, so that the
`j`-th factor has mass `≤ C/(j+1)`; extract one subsequence along which every factor and the total
`Γ_N = Σ_j α_{N,j}` converge weak-* (diagonal argument in the positive ball); put
`γ = Γ - Σ_j α_j`, positive as a limit of positive tails.  Splitting the formation into its first
`J` factors and its tail, the tail is within `e^{3RC} R² C²/(J+1)` of `Exp_⋆(z ⋅ tail sum)` uniformly
in `N` (`norm_prod_one_add_sub_exp_le`), and for fixed `J` the approximants converge weak-*
uniformly by the product and exponential continuity lemmas.

**Theorem 5.1 / Corollary 5.2.**  Conversely every decorated formation satisfying `(PDF.11)` is a
limit of finite packets `(α_1, …, α_J, γ/M, …, γ/M)` of mass `≤ C`, in norm uniformly on compact
sets (Lemma 3.1).  Hence the limits of finite formations of mass `≤ C` are exactly the decorated
formations, and every sequence of decorated formations has a convergent subsequence.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

/-! ### Formations -/

/-- The formation `Λ_A(z) = Π_j (δ_1 + z α_j)` of a finite packet `(PDF.2)`. -/
def formation {m : ℕ} (α : Fin m → MeasureAlgebra K) (z : ℂ) : MeasureAlgebra K :=
  ∏ j, (1 + z • α j)

/-- The packet mass `|A|_1 = Σ_j ‖α_j‖` `(PDF.3)`; for positive packets `‖α_j‖ = α_j(K)`. -/
def packetMass {m : ℕ} (α : Fin m → MeasureAlgebra K) : ℝ := ∑ j, ‖α j‖

/-- The decorated formation `Exp_⋆(z γ) ⋆ Π_j (δ_1 + z α_j)` `(PDF.12)`. -/
def decorated (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (z : ℂ) : MeasureAlgebra K :=
  exp (z • γ) * ∏' j, (1 + z • α j)

/-- Compact-open weak convergence `(PDF.5)`. -/
def FormConv (F : ℕ → ℂ → MeasureAlgebra K) (G : ℂ → MeasureAlgebra K) : Prop :=
  ∀ R : ℝ, WeakUnifOn F G (Metric.closedBall 0 R)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The infinite product converges in norm when the masses are summable. -/
theorem multipliable_formation {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖)
    (z : ℂ) : Multipliable fun j => 1 + z • α j :=
  multipliable_one_add_of_summable ((hα.mul_left ‖z‖).congr fun j => (norm_smul z (α j)).symm)

/-! ### The tail estimate -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **The tail estimate `(PDF.15)`–`(PDF.16)`**: if the factors beyond `J` have mass
`≤ C/(J+1)` and the total mass is `≤ C`, then
`‖Π_{j<L}(1 + zα_j) - Π_{j<J}(1 + zα_j) Exp_⋆(z Σ_{J≤j<L} α_j)‖ ≤ e^{3RC} R²C²/(J+1)`. -/
theorem norm_prod_range_sub_le (α : ℕ → MeasureAlgebra K) {z : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hz : ‖z‖ ≤ R) {J L : ℕ} (hJL : J ≤ L) (hmass : ∑ j ∈ Finset.range L, ‖α j‖ ≤ C)
    (htail : ∀ j, J ≤ j → ‖α j‖ ≤ C / (J + 1)) :
    ‖∏ j ∈ Finset.range L, (1 + z • α j) -
        (∏ j ∈ Finset.range J, (1 + z • α j)) * exp (z • ∑ j ∈ Finset.Ico J L, α j)‖ ≤
      Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1)) := by
  have hC : 0 ≤ C := (Finset.sum_nonneg fun j _ => norm_nonneg (α j)).trans hmass
  have hsplit : ∑ j ∈ Finset.range J, ‖α j‖ + ∑ j ∈ Finset.Ico J L, ‖α j‖ =
      ∑ j ∈ Finset.range L, ‖α j‖ := Finset.sum_range_add_sum_Ico _ hJL
  have hIco : ∑ j ∈ Finset.Ico J L, ‖α j‖ ≤ C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range J) => norm_nonneg (α j)
    linarith
  have hJ : ∑ j ∈ Finset.range J, ‖α j‖ ≤ C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.Ico J L) => norm_nonneg (α j)
    linarith
  rw [← Finset.prod_range_mul_prod_Ico _ hJL, ← mul_sub, Finset.smul_sum]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖∏ j ∈ Finset.range J, (1 + z • α j)‖ ≤ Real.exp (R * C) :=
    (norm_prod_one_add_le _ _ hz).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hJ hR))
  have h2 := norm_prod_one_add_sub_exp_le (Finset.Ico J L) fun j => z • α j
  have hn : ∀ j, ‖z • α j‖ ≤ R * ‖α j‖ := fun j => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hs1 : ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ≤ R * C := by
    calc ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ≤ ∑ j ∈ Finset.Ico J L, R * ‖α j‖ :=
          Finset.sum_le_sum fun j _ => hn j
      _ = R * ∑ j ∈ Finset.Ico J L, ‖α j‖ := by rw [Finset.mul_sum]
      _ ≤ R * C := mul_le_mul_of_nonneg_left hIco hR
  have hs2 : ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ^ 2 ≤ R ^ 2 * C ^ 2 / (J + 1) := by
    calc ∑ j ∈ Finset.Ico J L, ‖z • α j‖ ^ 2
        ≤ ∑ j ∈ Finset.Ico J L, R ^ 2 * (C / (J + 1)) * ‖α j‖ := Finset.sum_le_sum fun j hj => by
          have hjJ : J ≤ j := (Finset.mem_Ico.1 hj).1
          have h3 := hn j
          have h4 := htail j hjJ
          have h5 : ‖z • α j‖ ^ 2 ≤ (R * ‖α j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          calc ‖z • α j‖ ^ 2 ≤ (R * ‖α j‖) ^ 2 := h5
            _ = R ^ 2 * ‖α j‖ * ‖α j‖ := by ring
            _ ≤ R ^ 2 * (C / (J + 1)) * ‖α j‖ := by
                gcongr
      _ = R ^ 2 * (C / (J + 1)) * ∑ j ∈ Finset.Ico J L, ‖α j‖ := by rw [Finset.mul_sum]
      _ ≤ R ^ 2 * (C / (J + 1)) * C := mul_le_mul_of_nonneg_left hIco (by positivity)
      _ = R ^ 2 * C ^ 2 / (J + 1) := by ring
  calc ‖∏ j ∈ Finset.range J, (1 + z • α j)‖ *
        ‖∏ j ∈ Finset.Ico J L, (1 + z • α j) - exp (∑ j ∈ Finset.Ico J L, z • α j)‖
      ≤ Real.exp (R * C) * (Real.exp (2 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1))) :=
        mul_le_mul h1 (h2.trans (mul_le_mul (Real.exp_le_exp.2 (by linarith)) hs2
          (Finset.sum_nonneg fun j _ => by positivity) (Real.exp_pos _).le)) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = Real.exp (3 * (R * C)) * (R ^ 2 * C ^ 2 / (J + 1)) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

end GaloisForLFunctions.HTGeometry.FormationDust
