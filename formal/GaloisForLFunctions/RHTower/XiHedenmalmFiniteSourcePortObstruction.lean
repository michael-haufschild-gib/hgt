import GaloisForLFunctions.RHTower.XiHedenmalmInvariantHomogenization

/-!
# Finite source ports cannot homogenize the Hedenmalm theta system

Every complex function subspace containing the completed theta source `XiC` and stable under
spectral-coordinate multiplication contains the whole polynomial orbit `XiC·ℂ[z]`.  Because `XiC`
is analytic and nonzero at the spectral centre, multiplication by `XiC` is injective on
polynomials — a polynomial vanishing on a punctured neighbourhood of zero has infinitely many
roots — so the orbit vectors are linearly independent and the subspace cannot be
finite-dimensional.  No rank-two or fixed finite-rank compensating port can remove the affine
Hedenmalm source while retaining its descended generator.
-/

open Complex Polynomial

noncomputable section

namespace RHTower

/-- The polynomial source-orbit map `P ↦ P·XiC` of the Hedenmalm system. -/
def xiHedenmalmSourceOrbitMap : Polynomial ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun P := fun z => P.eval z * XiC z
  map_add' P Q := by
    funext z
    simp [add_mul]
  map_smul' c P := by
    funext z
    simp [smul_eq_mul, mul_assoc]

@[simp] theorem xiHedenmalmSourceOrbitMap_apply (P : Polynomial ℂ) (z : ℂ) :
    xiHedenmalmSourceOrbitMap P z = P.eval z * XiC z := rfl

/-- `XiC` is nonzero on a full metric ball around the spectral centre. -/
theorem exists_ball_XiC_ne_zero :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball (0 : ℂ) r, XiC z ≠ 0 := by
  have hcont : ContinuousAt XiC 0 := (XiC_analytic 0 (Set.mem_univ _)).continuousAt
  have hev : ∀ᶠ z in nhds (0 : ℂ), XiC z ≠ 0 := hcont.eventually_ne XiC_zero_ne
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨r, hr, hball⟩

/-- Multiplication by the theta source is injective on polynomials: the source germ is nonzero
at the centre, so a cancelled polynomial has infinitely many roots. -/
theorem xiHedenmalmSourceOrbitMap_injective :
    Function.Injective xiHedenmalmSourceOrbitMap := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  obtain ⟨r, hr, hball⟩ := exists_ball_XiC_ne_zero
  have hroots : {z : ℂ | P.IsRoot z}.Infinite := by
    have hsub : Metric.ball (0 : ℂ) r ⊆ {z : ℂ | P.IsRoot z} := by
      intro z hz
      have hz0 : P.eval z * XiC z = 0 := congrFun hP z
      have hXi : XiC z ≠ 0 := hball z hz
      exact mul_eq_zero.mp hz0 |>.resolve_right hXi
    have hinj : Function.Injective (fun n : ℕ => ((r / (n + 2) : ℝ) : ℂ)) := by
      intro m n hmn
      have hre : (r / (m + 2) : ℝ) = (r / (n + 2) : ℝ) := by
        exact_mod_cast congrArg Complex.re hmn
      have hm2 : (0 : ℝ) < m + 2 := by positivity
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      have : (m + 2 : ℝ) = (n + 2 : ℝ) := by
        field_simp at hre
        rcases hre with h | h
        · linarith [h]
        · exact absurd h hr.ne'
      exact_mod_cast by linarith [this]
    have hmem : ∀ n : ℕ, ((r / (n + 2) : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      intro n
      rw [Metric.mem_ball, dist_zero_right]
      have hn2 : (1 : ℝ) < n + 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hpos : 0 < r / (n + 2 : ℝ) := by positivity
      rw [Complex.norm_real, abs_of_pos hpos]
      rw [div_lt_iff (by positivity : (0 : ℝ) < n + 2)]
      nlinarith
    exact Set.infinite_of_injective_forall_mem hinj fun n => hsub (hmem n)
  exact Polynomial.eq_zero_of_infinite_isRoot P hroots

/-- **Finite source ports cannot homogenize the Hedenmalm theta system.**  Every complex
function subspace containing the completed theta source and stable under spectral-coordinate
multiplication is infinite-dimensional. -/
theorem xiHedenmalm_coordinateStable_sourcePort_not_finiteDimensional
    (S : Submodule ℂ (ℂ → ℂ)) (hXi : XiC ∈ S)
    (hstab : ∀ F ∈ S, xiCoordinateMultiplication F ∈ S) :
    ¬ FiniteDimensional ℂ S := by
  intro hfd
  set n := Module.finrank ℂ S + 1 with hn
  have hmem : ∀ k : ℕ, (fun z : ℂ => (Polynomial.X ^ k : Polynomial ℂ).eval z * XiC z) ∈ S :=
    fun k => eval_mul_XiC_mem_of_coordinateMultiplication_stable S hXi hstab (Polynomial.X ^ k)
  -- linear independence of the full monomial orbit
  have hmono : LinearIndependent ℂ fun k : ℕ => (Polynomial.X : Polynomial ℂ) ^ k := by
    have hb := (Polynomial.basisMonomials ℂ).linearIndependent
    have hXp : (fun k : ℕ => (Polynomial.X : Polynomial ℂ) ^ k) =
        fun k : ℕ => Polynomial.monomial k (1 : ℂ) := by
      funext k
      rw [Polynomial.X_pow_eq_monomial]
    rwa [hXp]
  have horbit : LinearIndependent ℂ
      (fun k : ℕ => xiHedenmalmSourceOrbitMap ((Polynomial.X : Polynomial ℂ) ^ k)) :=
    hmono.map' xiHedenmalmSourceOrbitMap
      (LinearMap.ker_eq_bot.mpr xiHedenmalmSourceOrbitMap_injective)
  have hfin : LinearIndependent ℂ
      (fun k : Fin n => xiHedenmalmSourceOrbitMap ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ))) :=
    horbit.comp (fun k : Fin n => (k : ℕ)) Fin.val_injective
  -- transport the family into the submodule
  have hSfam : LinearIndependent ℂ
      (fun k : Fin n =>
        (⟨fun z : ℂ => ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).eval z * XiC z,
          hmem (k : ℕ)⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype
    convert hfin using 1
  have hcard := hSfam.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end RHTower

end
