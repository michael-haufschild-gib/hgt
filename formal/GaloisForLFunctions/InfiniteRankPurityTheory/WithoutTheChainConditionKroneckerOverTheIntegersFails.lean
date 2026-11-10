import GaloisForLFunctions.InfiniteRankPurityTheory.KroneckerOverTheIntegersNeedsNoDistinctModes
import GaloisForLFunctions.HTGeometry.CircleQuadraturePositiveWolffMeasure

/-!
# Without the chain condition Kronecker over the integers fails

Kronecker's theorem over `ℤ`, the uniqueness of a module with given traces, and the growth form of
the weight filtration all assume that the weights `Re ρ_i` have no infinite ascending chain. This
module shows that the assumption cannot be dropped.

* `frobTrace_eq_tsum_of_powerSums_zero`: a module with summable weights and bounded modes whose
  power sums `Σ_i c_i ρ_i^k` vanish for every `k ≥ 1` has the constant trace `Σ_i c_i` at every
  `x > 0`: `x^{ρ} = Σ_k (ρ log x)^k / k!`, and the double series may be summed over `i` first.
* `frobTrace_wolff`, `exists_integral_traceClass_module_not_tate`: the nodes and masses of a
  positive Wolff measure (`HTGeometry.CircleQuadraturePositive`), normalized to total mass one, form
  a module with distinct modes of modulus `≤ 10`, positive weights, of trace class of every order at
  the identity, whose trace is `1` at every `x > 0`, and which carries weight at the mode `5/4`.
* `wolff_not_weightsWellFounded`: its weights have an ascending chain.

So without the chain condition an integral trace-class module need not be Tate, two different
modules have the same trace at every Frobenius, and a bounded trace does not bound the weights.
The chain condition is the exact hypothesis of the three theorems.
-/

open Filter Topology

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open GaloisForLFunctions.HTGeometry.CircleQuadraturePositive

/-- **Vanishing power sums give a constant trace.** -/
theorem frobTrace_eq_tsum_of_powerSums_zero {ι : Type*} {c ρ : ι → ℂ}
    (hc : Summable fun i => ‖c i‖) {R : ℝ} (hR : ∀ i, ‖ρ i‖ ≤ R)
    (h0 : ∀ k : ℕ, 1 ≤ k → HasSum (fun i => c i * ρ i ^ k) 0) {x : ℝ} (hx : 0 < x) :
    frobTrace c ρ x = ∑' i, c i := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
  -- each term is an exponential series in `ρ_i log x`
  have hterm : ∀ i, c i * (x : ℂ) ^ ρ i =
      ∑' k : ℕ, c i * (((Real.log x : ℂ) * ρ i) ^ k / (k.factorial : ℂ)) := by
    intro i
    rw [Complex.cpow_def_of_ne_zero hxc, hlog, tsum_mul_left, Complex.exp_eq_exp_ℂ,
      (NormedSpace.expSeries_div_hasSum_exp ((Real.log x : ℂ) * ρ i)).tsum_eq]
  -- the double series converges absolutely
  have hsum : Summable (Function.uncurry fun (i : ι) (k : ℕ) =>
      c i * (((Real.log x : ℂ) * ρ i) ^ k / (k.factorial : ℂ))) := by
    have hmaj : Summable fun p : ι × ℕ =>
        ‖c p.1‖ * ((‖(Real.log x : ℂ)‖ * |R|) ^ p.2 / (p.2.factorial : ℝ)) :=
      Summable.mul_of_nonneg hc (Real.summable_pow_div_factorial _) (fun i => norm_nonneg _)
        fun k => div_nonneg (pow_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) k)
          (Nat.cast_nonneg _)
    refine Summable.of_norm_bounded hmaj fun p => ?_
    simp only [Function.uncurry]
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      (norm_nonneg _)
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left ((hR p.1).trans (le_abs_self R)) (norm_nonneg _)) _
  rw [frobTrace]
  simp_rw [hterm]
  rw [← hsum.tsum_comm, tsum_eq_single 0]
  · simp
  · intro k hk
    have h := (h0 k (Nat.one_le_iff_ne_zero.mpr hk)).mul_left
      ((Real.log x : ℂ) ^ k / (k.factorial : ℂ))
    rw [mul_zero] at h
    rw [← h.tsum_eq]
    refine tsum_congr fun i => ?_
    rw [mul_pow]
    ring

/-! ### The Wolff module -/

/-- The total mass of the positive Wolff measure. -/
noncomputable def wolffMass : ℝ := ∑' i : PIdx, pcoef i

/-- The weights of the Wolff module: the masses, normalized to total mass one. -/
noncomputable def wolffWeight (i : PIdx) : ℂ := (pcoef i : ℂ) / (wolffMass : ℂ)

/-- The base node `5/4`. -/
def wolffBase : PIdx := ⟨0, ⟨0, show 0 < pcount 0 from Nat.one_pos⟩⟩

theorem ppoint_wolffBase : ppoint wolffBase = 5 / 4 := rfl

theorem wolffMass_pos : 0 < wolffMass :=
  summable_pcoef.tsum_pos (fun i => (pcoef_pos i).le) wolffBase (pcoef_pos _)

theorem wolffWeight_ne_zero (i : PIdx) : wolffWeight i ≠ 0 :=
  div_ne_zero (by exact_mod_cast (pcoef_pos i).ne') (by exact_mod_cast wolffMass_pos.ne')

theorem norm_wolffWeight (i : PIdx) : ‖wolffWeight i‖ = pcoef i / wolffMass := by
  rw [wolffWeight, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (pcoef_pos i).le, Real.norm_of_nonneg wolffMass_pos.le]

theorem summable_norm_wolffWeight : Summable fun i : PIdx => ‖wolffWeight i‖ := by
  simp_rw [norm_wolffWeight]
  exact summable_pcoef.div_const _

/-- The Wolff module is of trace class of every order at the identity. -/
theorem summable_wolffWeight_order (m : ℕ) :
    Summable fun i : PIdx => ‖wolffWeight i‖ * (1 + ‖ppoint i‖) ^ m := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _)
    (pow_nonneg (by linarith [norm_nonneg (ppoint i)]) _)) (fun i => ?_)
    (summable_norm_wolffWeight.mul_right ((11 : ℝ) ^ m))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [norm_nonneg (ppoint i)])
    (by linarith [norm_ppoint_le i]) m) (norm_nonneg _)

/-- **The trace of the Wolff module is `1` at every Frobenius.** -/
theorem frobTrace_wolff {x : ℝ} (hx : 0 < x) : frobTrace wolffWeight ppoint x = 1 := by
  have hW : (wolffMass : ℂ) ≠ 0 := by exact_mod_cast wolffMass_pos.ne'
  have h0 : ∀ k : ℕ, 1 ≤ k → HasSum (fun i : PIdx => wolffWeight i * ppoint i ^ k) 0 := by
    intro k hk
    have h := (hasSum_pcoef_mul_ppoint_pow hk).div_const (wolffMass : ℂ)
    rw [zero_div] at h
    have hfun : (fun i : PIdx => wolffWeight i * ppoint i ^ k) =
        fun i => (pcoef i : ℂ) * ppoint i ^ k / (wolffMass : ℂ) := by
      funext i
      rw [wolffWeight, div_mul_eq_mul_div]
    rw [hfun]
    exact h
  rw [frobTrace_eq_tsum_of_powerSums_zero summable_norm_wolffWeight norm_ppoint_le h0 hx]
  simp_rw [wolffWeight]
  rw [tsum_div_const, ← Complex.ofReal_tsum]
  exact div_self hW

/-- **An integral trace-class module that is not Tate.** Distinct bounded modes, nonzero weights,
trace class of every order, trace `1` at every `x > 0`, and a visible mode `5/4`. -/
theorem exists_integral_traceClass_module_not_tate :
    ∃ (ι : Type) (b ρ : ι → ℂ), Function.Injective ρ ∧ (∀ i, ‖ρ i‖ ≤ 10) ∧ (∀ i, b i ≠ 0) ∧
      (∀ m : ℕ, Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) ∧
      (∀ x : ℝ, 0 < x → frobTrace b ρ x = 1) ∧ ∃ i, ρ i = 5 / 4 :=
  ⟨PIdx, wolffWeight, ppoint, ppoint_injective, norm_ppoint_le, wolffWeight_ne_zero,
    summable_wolffWeight_order, fun _ hx => frobTrace_wolff hx, wolffBase, ppoint_wolffBase⟩

/-- **The chain condition is necessary.** The weights of the Wolff module have an ascending chain:
otherwise Kronecker's theorem would make its visible mode `5/4` a natural number. -/
theorem wolff_not_weightsWellFounded : ¬ WeightsWellFounded ppoint := by
  intro hwf
  have hA : ∀ i : PIdx, (ppoint i).re ≤ 10 := fun i =>
    (Complex.re_le_norm _).trans (norm_ppoint_le i)
  have hint : ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, frobTrace wolffWeight ppoint n = k := fun n hn =>
    ⟨1, by rw [frobTrace_wolff (by exact_mod_cast hn)]; simp⟩
  obtain ⟨k, -, hk⟩ := tate_of_integral_trace (m := 11) ppoint_injective hwf hA (by norm_num)
    (summable_wolffWeight_order 11) hint wolffBase (wolffWeight_ne_zero _)
  rw [ppoint_wolffBase] at hk
  have hre := congrArg Complex.re hk
  have h4 : (5 : ℝ) = 4 * (k : ℝ) := by
    have h5 : ((5 / 4 : ℂ)).re = 5 / 4 := by norm_num
    rw [h5, Complex.natCast_re] at hre
    linarith
  have h4' : (5 : ℕ) = 4 * k := by exact_mod_cast h4
  omega

end GaloisForLFunctions.InfiniteRankPurityTheory
