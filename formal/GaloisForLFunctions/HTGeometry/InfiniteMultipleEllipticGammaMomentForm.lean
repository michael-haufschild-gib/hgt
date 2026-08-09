import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaMoments
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaFreeEnergy

/-!
# The free energy in moment form

The logarithm tails of the occupation spectrum form a double family, indexed by the occupation and
by the tail order.  Each term is majorised by a product of a factor depending only on the occupation
and a factor depending only on the order, so the double family is absolutely summable and the two
sums may be interchanged.

Interchanging turns the summed tails into the moment series, whose coefficients are the nome Euler
products.  This is the card's regularized free energy.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- Per-term majorant of a logarithm-tail term: a factor in the occupation times a factor in the
tail order. -/
theorem norm_logTail_term_le (g m : ℕ) {x q : ℂ} (hq : ‖q‖ ≤ 1) :
    ‖(x * q) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖
      ≤ ‖x‖ ^ (g + 1) / ((g : ℝ) + 1) * (‖q‖ ^ (g + 1) * ‖x‖ ^ m) := by
  have hD : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hcast : ((m + (g + 1) : ℕ) : ℝ) = (m : ℝ) + ((g : ℝ) + 1) := by push_cast; ring
  have hge : ((g : ℝ) + 1) ≤ ((m + (g + 1) : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hval : ‖(x * q) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖
      = ‖x‖ ^ (m + (g + 1)) * ‖q‖ ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ) := by
    rw [norm_div, norm_pow, norm_mul, mul_pow, Complex.norm_natCast]
  have hnum : ‖x‖ ^ (m + (g + 1)) * ‖q‖ ^ (m + (g + 1))
      ≤ ‖x‖ ^ (g + 1) * ‖x‖ ^ m * ‖q‖ ^ (g + 1) := by
    have h1 : ‖q‖ ^ (m + (g + 1)) ≤ ‖q‖ ^ (g + 1) :=
      pow_le_pow_of_le_one (norm_nonneg _) hq (by omega)
    have h2 : ‖x‖ ^ (m + (g + 1)) = ‖x‖ ^ (g + 1) * ‖x‖ ^ m := by
      rw [pow_add]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hshuffle : ‖x‖ ^ (g + 1) / ((g : ℝ) + 1) * (‖q‖ ^ (g + 1) * ‖x‖ ^ m)
      = (‖x‖ ^ (g + 1) * ‖x‖ ^ m * ‖q‖ ^ (g + 1)) / ((g : ℝ) + 1) := by
    ring
  rw [hval, hshuffle]
  exact div_le_div₀ (by positivity) hnum hD hge

/-- The double family of logarithm-tail terms is absolutely summable. -/
theorem summable_logTail_family {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (Function.uncurry (fun (ν : ι →₀ ℕ) (m : ℕ) =>
      (x * nomeMonomial p ν) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ))) := by
  have hq_sum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  have hmaj : Summable (fun z : (ι →₀ ℕ) × ℕ =>
      ‖x‖ ^ (g + 1) / ((g : ℝ) + 1) *
        (‖nomeMonomial p z.1‖ ^ (g + 1) * ‖x‖ ^ z.2)) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg hq_sum (summable_geometric_of_lt_one (norm_nonneg x) hx)
      (fun ν => by positivity) (fun m => by positivity)
  refine Summable.of_norm_bounded hmaj ?_
  rintro ⟨ν, m⟩
  exact norm_logTail_term_le g m (norm_nomeMonomial_le_one p hp_lt ν)

/-- The occupation sum of one tail order is the moment coefficient. -/
theorem tsum_logTail_family_occupation {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (x : ℂ) (m : ℕ) :
    (∑' ν : ι →₀ ℕ, (x * nomeMonomial p ν) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ))
      = x ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
        ∏' a, (1 - p a ^ (m + (g + 1)))⁻¹ := by
  have hrw : ∀ ν : ι →₀ ℕ,
      (x * nomeMonomial p ν) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)
        = x ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
          (nomeMonomial p ν) ^ (m + (g + 1)) := by
    intro ν
    rw [mul_pow]
    ring
  rw [tsum_congr hrw, tsum_mul_left]
  congr 1
  exact tsum_nomeMonomial_pow p hp_lt (by omega)
    (summable_norm_pow_of_le hp_lt (by omega) hsum)

/-- **The regularized free energy in moment form.**  Inside the unit disc the infinite-order product
is the exponential of minus the moment series, whose coefficients are the nome Euler products at the
corresponding powers. -/
theorem infiniteMultipleEllipticGamma_eq_exp_neg_moments {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    infiniteMultipleEllipticGamma g p x
      = Complex.exp (-∑' m : ℕ, x ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
          ∏' a, (1 - p a ^ (m + (g + 1)))⁻¹) := by
  have hcomm := (summable_logTail_family g p hp_lt hsum hx).tsum_comm
  rw [infiniteMultipleEllipticGamma_eq_exp_neg_tsum g p hp_lt hsum hx]
  congr 2
  have htail : ∀ ν : ι →₀ ℕ, primaryLogTail g (x * nomeMonomial p ν)
      = ∑' m : ℕ, (x * nomeMonomial p ν) ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) := by
    intro ν
    rw [primaryLogTail]
  rw [tsum_congr htail, ← hcomm]
  exact tsum_congr (tsum_logTail_family_occupation g p hp_lt hsum x)

end HTGeometry
