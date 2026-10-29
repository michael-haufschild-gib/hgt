import GaloisForLFunctions.ArithmeticKreinLangerTheory.CyclicSubgroupsDecideTheKreinLangerClass
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# The index is continuous off the discriminant

Bounded index is closed under pointwise convergence of kernels, so the index can only drop in a
limit. This module identifies exactly where it drops for Krein–Langer data, and so names the
topology that carries the index: pointwise convergence of the data `(p, χ_j, ω_j)` away from the
**discriminant**, where a node reaches the unit circle, two nodes collide, or a weight vanishes.

**Lower semicontinuity, attained** (`eventually_le_negIndex_of_tendsto`). A finite index of the
limit is attained on one finite family, and the Gram matrices of that family converge, so
eventually every approximant has at least the limit's index.

**Continuity off the discriminant** (`eventually_negIndex_eq_of_tendsto`). If positive-definite
parts converge pointwise, the `κ` characters converge pointwise, the weights converge to nonzero
limits, and the limit data are separated at one element, then eventually every approximant has
index exactly `κ`: the structural ceiling `κ` meets the semicontinuous floor.

**The three degenerations** (`vanishing_weight_drops_index`, `collision_drops_index`, and HKT's
`coalescence_law`). Each part of the discriminant lowers the index: a weight `t → 0` takes a pair
of index one to the zero kernel; two logarithmic pairs with opposite weights whose exponents collide
take index two to zero; a pair whose exponent reaches the critical line loses its square when its
weight has nonnegative real part.

For the Weil kernel the receivers HKT builds (height truncations, integer windows, shrinking atoms)
add pairs monotonically and never cross the discriminant, which is why their indices converge to
`κ(K_ζ)`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {G : Type*} [Group G]

/-- **Lower semicontinuity, attained.** If `k_n → k₀` pointwise and `κ(k₀)` is finite, eventually
`κ(k₀) ≤ κ(k_n)`. -/
theorem eventually_le_negIndex_of_tendsto {β : Type*} {l : Filter β} {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g))) (hh₀ : IsHermKernel k₀)
    (h₀ : negIndex k₀ < ⊤) : ∀ᶠ n in l, negIndex k₀ ≤ negIndex (k n) := by
  obtain ⟨m, x, hx⟩ := exists_hermNegIndex_gram_eq_negIndex h₀
  filter_upwards [eventually_le_hermNegIndex (H := fun n => gram (k n) x)
    (gram_isHermitian hh₀ x) fun a b => hk _] with n hn
  rw [← hx]
  exact (Nat.cast_le.mpr hn).trans (hermNegIndex_gram_le_negIndex _ _)

/-- Pair kernels depend continuously on the character values and the weight. -/
theorem tendsto_pairKernel {β : Type*} {l : Filter β} {χ : β → G →* ℂ} {χ₀ : G →* ℂ}
    (hχ : ∀ g, Tendsto (fun n => χ n g) l (𝓝 (χ₀ g))) {ω : β → ℂ} {ω₀ : ℂ}
    (hω : Tendsto ω l (𝓝 ω₀)) (g : G) :
    Tendsto (fun n => pairKernel (χ n) (ω n) g) l (𝓝 (pairKernel χ₀ ω₀ g)) := by
  simp only [pairKernel, reflectChar_apply]
  exact (hω.mul (hχ g)).add (((continuous_conj.tendsto _).comp hω).mul
    ((continuous_conj.tendsto _).comp (hχ g⁻¹)))

/-- **Continuity of the index off the discriminant.** Converging Krein–Langer data whose limit has
nonzero weights and is separated at one element have, eventually, exactly `κ` negative squares. -/
theorem eventually_negIndex_eq_of_tendsto {κ : ℕ} {β : Type*} {l : Filter β} [l.NeBot]
    {p : β → G → ℂ} {p₀ : G → ℂ} (hp : ∀ n, IsPosDefKernel (p n))
    (hpc : ∀ g, Tendsto (fun n => p n g) l (𝓝 (p₀ g)))
    {χ : β → Fin κ → G →* ℂ} {χ₀ : Fin κ → G →* ℂ}
    (hχ : ∀ j g, Tendsto (fun n => χ n j g) l (𝓝 (χ₀ j g)))
    {ω : β → Fin κ → ℂ} {ω₀ : Fin κ → ℂ} (hω : ∀ j, Tendsto (fun n => ω n j) l (𝓝 (ω₀ j)))
    (hω₀ : ∀ j, ω₀ j ≠ 0) (u : G) (hne : ∀ j, ‖χ₀ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ₀ u)) :
    ∀ᶠ n in l, negIndex (fun g => p n g + ∑ j, pairKernel (χ n j) (ω n j) g) = κ := by
  have hp₀ : IsPosDefKernel p₀ := isPosDefKernel_of_tendsto hpc (Eventually.of_forall hp)
  have hlim := negIndex_add_sum_pairKernel_eq hp₀ χ₀ ω₀ hω₀ u hne hsep
  have hconv : ∀ g, Tendsto (fun n => p n g + ∑ j, pairKernel (χ n j) (ω n j) g) l
      (𝓝 (p₀ g + ∑ j, pairKernel (χ₀ j) (ω₀ j) g)) := fun g =>
    (hpc g).add (tendsto_finsetSum _ fun j _ => tendsto_pairKernel (hχ j) (hω j) g)
  have hh₀ : IsHermKernel fun g => p₀ g + ∑ j, pairKernel (χ₀ j) (ω₀ j) g :=
    hp₀.1.add (isHermKernel_finset_sum _ fun j _ => isHermKernel_pairKernel _ _)
  filter_upwards [eventually_le_negIndex_of_tendsto hconv hh₀ (by rw [hlim]; exact ENat.coe_lt_top _)]
    with n hn
  refine le_antisymm ?_ (hlim ▸ hn)
  simpa using negIndex_add_sum_pairKernel_le (hp n) (χ n) (ω n)

/-! ### The three degenerations -/

/-- **A vanishing weight drops the index.** The pair `h_{χ,t}` of a non-unitary character has index
one for every `t ≠ 0` and tends to the zero kernel as `t → 0`. -/
theorem vanishing_weight_drops_index {χ : G →* ℂ} (hχ : ¬ IsUnitaryChar χ) :
    (∀ t : ℂ, t ≠ 0 → negIndex (pairKernel χ t) = 1) ∧
      (∀ g, Tendsto (fun t : ℂ => pairKernel χ t g) (𝓝 0) (𝓝 0)) ∧
      negIndex (0 : G → ℂ) = 0 := by
  refine ⟨fun t ht => by simpa using negIndex_add_pairKernel_eq_one isPosDefKernel_zero hχ ht,
    fun g => ?_, isPosDefKernel_zero.negIndex_eq_zero⟩
  have := tendsto_pairKernel (χ := fun _ : ℂ => χ) (χ₀ := χ) (fun g => tendsto_const_nhds)
    (ω := id) (ω₀ := 0) tendsto_id g
  simpa [pairKernel] using this

/-- **A collision drops the index.** On `ℚ_{>0}`, two logarithmic pairs with exponents `s` and
`s + 1/(n+1)` (`Re s > 0`) and opposite weights have index two for every `n`, and their limit, the
collided pair with weight `1 − 1 = 0`, is the zero kernel. -/
theorem collision_drops_index {s : ℂ} (hs : 0 < s.re) :
    (∀ n : ℕ, negIndex (fun g => (0 : HeckeLattice → ℂ) g + ∑ j, pairKernel
      (logChar heckeLogScale (![s, s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)] j)) (![1, -1] j) g) = 2) ∧
    (∀ g, Tendsto (fun n : ℕ => (0 : HeckeLattice → ℂ) g + ∑ j, pairKernel
      (logChar heckeLogScale (![s, s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)] j)) (![1, -1] j) g)
        atTop (𝓝 0)) := by
  refine ⟨fun n => ?_, fun g => ?_⟩
  · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine negIndex_logChar_pairs_eq heckeLogScale heckeLogScale_small isPosDefKernel_zero _
      (fun i j h => ?_) (fun j => ?_) _ (fun j => by fin_cases j <;> simp)
    · have hne : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one] at h ⊢
      · exact absurd (add_eq_left.mp h.symm) hne
      · exact absurd (add_eq_left.mp h) hne
    · fin_cases j
      · simpa using hs
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_re, ofReal_re]
        linarith
  · simp only [Pi.zero_apply, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hlim : Tendsto (fun n : ℕ => s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 s) := by
      simpa using tendsto_const_nhds.add
        ((continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat)
    have hχ : ∀ g', Tendsto (fun n : ℕ => logChar heckeLogScale
        (s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) g') atTop (𝓝 (logChar heckeLogScale s g')) := fun g' => by
      simp only [logChar_apply]
      exact (Complex.continuous_exp.tendsto _).comp (hlim.mul tendsto_const_nhds)
    have h2 := tendsto_pairKernel hχ (tendsto_const_nhds (x := (-1 : ℂ))) g
    have h1 := (tendsto_const_nhds (x := pairKernel (logChar heckeLogScale s) 1 g)).add h2
    convert h1 using 2
    simp only [pairKernel, map_one, map_neg, one_mul, neg_mul]
    ring

end GaloisForLFunctions.ArithmeticKreinLangerTheory

#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.eventually_negIndex_eq_of_tendsto
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.vanishing_weight_drops_index
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.collision_drops_index
