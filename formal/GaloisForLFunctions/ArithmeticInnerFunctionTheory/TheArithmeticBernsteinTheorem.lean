import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheTorusWallsOfPrimeInsertion
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.RHTower.MobiusPrimeApertureDifferentialOrder

/-!
# An arithmetic Bernstein theorem: the largest insertion cone

Which amplitudes have nonnegative insertions at every prime set, phase and base point? The exponentially convex ones, and only those.

**Theorem** (`isExpConvex_of_torusPositive`). Let `f` be continuous on `ℝ`, of exponential decay at `+∞`, and
`|f(y)| ≤ C e^{κ|y|}` at `−∞` with `κ < ½`. If `f` has nonnegative torus sums on every finite set of primes at every base point, then every
Hankel form `Σ c_v c_w f(y + v + w)` is nonnegative. With `IsExpConvexFrom.torusSum` this classifies the cone
(`torusPositive_iff_expConvex`): by Bernstein–Widder, its members are the Laplace mixtures.

**Mechanism.** Against the Sato–Tate measures, the Hecke form on the primes of a window is
`f(x) Σ d_p² + Σ_{p,q} d_p d_q f(x + log p + log q)`. Spread a coefficient `c_v` over the primes near `e^{u+v}`, `x = y − 2u`: the double sum tends to the Hankel form
of `f` at `y`, and the diagonal cost is `f(y − 2u) Σ_v c_v²/#primes`, of size `e^{2κu}·u e^{−u}`. It vanishes exactly for
`κ < ½`. The critical exponent is the density of the primes: `Σ_p p^{−2s}` diverges at `s = ½`.

So phase locking at a fixed amplitude cannot enlarge the Laplace cone. The theta amplitude `A` of route TH, which is log-concave, grows
at exactly the critical rate `e^{|x|/2}` on the left.
-/

open Filter Topology Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Primes in multiplicative windows -/

/-- **Primes in `(X, e^ε X]`.** By the prime number theorem there are at least `c X / log X` of them. -/
theorem exists_card_primes_window_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X, X₀ ≤ X →
      c * (X / Real.log X) ≤ ((primesInIoc ⌊X⌋₊ ⌊Real.exp ε * X⌋₊).card : ℝ) := by
  set lam : ℝ := Real.exp ε with hlam
  have hlam1 : 1 < lam := Real.one_lt_exp_iff.mpr hε
  have hR := _root_.RHTower.tendsto_primeCounting_ratio
  have hscale : Tendsto (fun X : ℝ => lam * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have hR2 := hR.comp hscale
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hq : Tendsto (fun X : ℝ => Real.log X / Real.log (lam * X)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun X : ℝ => (Real.log lam / Real.log X + 1)⁻¹) atTop (𝓝 (0 + 1)⁻¹) :=
      ((tendsto_const_nhds.div_atTop hlog).add tendsto_const_nhds).inv₀ (by norm_num)
    have h2 : (0 + 1 : ℝ)⁻¹ = 1 := by norm_num
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with X hX
    have hl : 0 < Real.log X := Real.log_pos hX
    rw [Real.log_mul (by linarith) (by linarith)]
    have hl2 : 0 < Real.log lam := Real.log_pos hlam1
    field_simp
    ring
  -- `(π(λX) − π(X)) log X / X → λ − 1`
  have hmain : Tendsto (fun X : ℝ =>
      ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) / ((lam * X) / Real.log (lam * X))) * lam *
        (Real.log X / Real.log (lam * X)) - (Nat.primeCounting ⌊X⌋₊ : ℝ) / (X / Real.log X)) atTop
      (𝓝 (1 * lam * 1 - 1)) :=
    ((hR2.mul_const lam).mul hq).sub hR
  have hgoal : (1 : ℝ) * lam * 1 - 1 = lam - 1 := by ring
  rw [hgoal] at hmain
  have hev := hmain.eventually (lt_mem_nhds (show (lam - 1) / 2 < lam - 1 by linarith))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop 1))
  refine ⟨(lam - 1) / 2, by linarith, max X₁ 2, by
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun X hX => ?_⟩
  obtain ⟨h1, hX1⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hX0 : 0 < X := by linarith
  have hfloor : ⌊X⌋₊ ≤ ⌊lam * X⌋₊ := Nat.floor_le_floor (by nlinarith)
  rw [card_primesInIoc hfloor]
  have hYpos : 0 < lam * X := by positivity
  have hlY : 0 < Real.log (lam * X) := Real.log_pos (by nlinarith)
  have e : ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) / ((lam * X) / Real.log (lam * X))) * lam *
      (Real.log X / Real.log (lam * X)) - (Nat.primeCounting ⌊X⌋₊ : ℝ) / (X / Real.log X) =
      ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊) * (Real.log X / X) := by
    field_simp
  rw [e] at h1
  have hfrac : 0 < X / Real.log X := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1.le hfrac.le
  have e2 : ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊) * (Real.log X / X) *
      (X / Real.log X) = (Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊ := by
    field_simp
  rw [e2] at h2
  exact h2

/-! ### The Hecke form on primes -/

variable {n : ℕ}

theorem ampl_zero (f : ℝ → ℝ) (ℓ : Fin n → ℝ) (x : ℝ) : ampl f ℓ x 0 = f x := by
  simp [ampl]

theorem ampl_unit_add_unit (f : ℝ → ℝ) (ℓ : Fin n → ℝ) (x : ℝ) (i j : Fin n) :
    ampl f ℓ x (unitIdx i + unitIdx j) = f (x + ℓ i + ℓ j) := by
  have e : ∑ k, (((unitIdx i + unitIdx j) k : ℕ) : ℝ) * ℓ k = ℓ i + ℓ j := by
    simp only [unitIdx, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
  rw [ampl, e, add_assoc]

/-- The Hecke form with no constant term: `f(x) Σ d_i² + Σ_{i,j} d_i d_j f(x + ℓ_i + ℓ_j) ≥ 0`. -/
theorem hecke_primes_nonneg {f : ℝ → ℝ} {ℓ : Fin n → ℝ} {x : ℝ}
    (ha : TraceSummable (ampl f ℓ x)) (hpos : ∀ θ, 0 ≤ torusSum (ampl f ℓ x) θ) (d : Fin n → ℝ) :
    0 ≤ f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) := by
  have h := hecke_level_one ha hpos 0 d
  have e : heckeOne (ampl f ℓ x) 0 d =
      f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) := by
    rw [heckeOne]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, zero_add,
      ampl_zero, ampl_unit_add_unit, Finset.mul_sum]
    have hsplit : ∀ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) = d i ^ 2 * f (x + ℓ i + ℓ i) +
        ∑ j ∈ Finset.univ.erase i, d i * d j * f (x + ℓ i + ℓ j) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, ← add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e] at h
  exact h

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
