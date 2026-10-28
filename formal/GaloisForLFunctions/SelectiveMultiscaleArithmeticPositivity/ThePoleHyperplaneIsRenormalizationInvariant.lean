import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveGardingInequality
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheCompleteSourceIsADyadicMultiresolution

/-!
# The pole hyperplane is renormalization invariant

The dyadic renormalization step translates by `log 2`. On atomic tests it is the **dyadic shift**
`(Sx)_{2m} = x_m`, `(Sx)_n = 0` for odd `n`: the atom at `log m` moves to `log 2m`.

* **The shift is the translation** (`atomicTest_dyadicShift`):
  `f_{Sx}` at horizon `2N` is `T_{log 2} f_x`. So Weil's form is unchanged
  (`weilQuad_atomicTest_dyadicShift`), and so is the mass (`sum_sq_dyadicShift`).
* **The harmonic coordinate scales** (`harmonicSum_dyadicShift`): `ℓ_{2N}(Sx) = ℓ_N(x)/√2`. The
  harmonic hyperplane is invariant under renormalization (`harmonicSum_dyadicShift_eq_zero`).
* **Multiresolution combinations stay on the hyperplane** (`harmonicSum_add`, `atomicTest_add`):
  sums of hyperplane tests at different dyadic levels, embedded at the finest horizon, are
  hyperplane tests. Their pole term vanishes (`weilQuad_atomicTest_eq_markov_of_harmonic`), and the
  gap-paid bound applies to the whole combination (`exists_weilQuad_twoLevel_ge`).

The pole couplings between levels grow like `2^{|j − k|/2}` on general tests. On the hyperplane they
vanish identically, so there the only cross-level couplings are archimedean and prime.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-- The **dyadic shift** of atomic weights: the atom at `log m` moves to `log 2m`. -/
def dyadicShift (x : ℕ → ℝ) (n : ℕ) : ℝ := if n % 2 = 0 then x (n / 2) else 0

theorem dyadicShift_odd (x : ℕ → ℝ) (N : ℕ) : dyadicShift x (2 * N + 1) = 0 := by
  simp [dyadicShift, Nat.add_mod]

theorem dyadicShift_even (x : ℕ → ℝ) (m : ℕ) : dyadicShift x (2 * m) = x m := by
  simp [dyadicShift]

/-- A sum over `1, …, 2(N + 1)` adds the two new terms to the sum over `1, …, 2N`. -/
theorem sum_Icc_two_mul_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 (2 * (N + 1)), f n = ∑ n ∈ Icc 1 (2 * N), f n + f (2 * N + 1) + f (2 * N + 2) := by
  rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_Icc_succ_top (by omega),
    sum_Icc_succ_top (by omega)]

/-- Odd terms vanish, so the shifted sum over `1, …, 2N` is the sum over the even points. -/
theorem sum_dyadicShift (x : ℕ → ℝ) (F : ℕ → ℝ → ℝ) (hF : ∀ n, F n 0 = 0) (N : ℕ) :
    ∑ n ∈ Icc 1 (2 * N), F n (dyadicShift x n) = ∑ m ∈ Icc 1 N, F (2 * m) (x m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_two_mul_succ, ih, dyadicShift_odd, hF, add_zero, sum_Icc_succ_top (by omega),
      show 2 * N + 2 = 2 * (N + 1) by ring, dyadicShift_even]

/-- **The dyadic shift is the translation by `log 2`**: `f_{Sx} = T_{log 2} f_x`. -/
theorem atomicTest_dyadicShift (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest (2 * N) (dyadicShift x) g = translate (Real.log 2) (atomicTest N x g) := by
  funext u
  simp only [atomicTest, translate]
  rw [sum_dyadicShift x (fun n a => a * g (u - Real.log n)) (fun _ => zero_mul _)]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hm0.ne']
  ring_nf

/-- **Renormalization does not change Weil's form.** -/
theorem weilQuad_atomicTest_dyadicShift (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    weilQuad (atomicTest (2 * N) (dyadicShift x) g) = weilQuad (atomicTest N x g) := by
  rw [atomicTest_dyadicShift]
  exact weilQuadTw_comp_sub (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) _ _

/-- The dyadic shift preserves the mass of the weights. -/
theorem sum_sq_dyadicShift (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (2 * N), dyadicShift x n ^ 2 = ∑ m ∈ Icc 1 N, x m ^ 2 :=
  sum_dyadicShift x (fun _ a => a ^ 2) (fun _ => by norm_num) N

/-- **The harmonic coordinate scales by `1/√2`**: `ℓ_{2N}(Sx) = ℓ_N(x)/√2`. -/
theorem harmonicSum_dyadicShift (N : ℕ) (x : ℕ → ℝ) :
    harmonicSum (2 * N) (dyadicShift x) = harmonicSum N x / Real.sqrt 2 := by
  rw [harmonicSum, harmonicSum, sum_dyadicShift x (fun n a => a / Real.sqrt n)
    (fun _ => zero_div _), sum_div]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_div,
    mul_comm (Real.sqrt m)]

/-- **The harmonic hyperplane is renormalization invariant.** -/
theorem harmonicSum_dyadicShift_eq_zero {N : ℕ} {x : ℕ → ℝ} (hx : harmonicSum N x = 0) :
    harmonicSum (2 * N) (dyadicShift x) = 0 := by
  rw [harmonicSum_dyadicShift, hx, zero_div]

/-- The harmonic coordinate is additive. -/
theorem harmonicSum_add (N : ℕ) (x y : ℕ → ℝ) :
    harmonicSum N (x + y) = harmonicSum N x + harmonicSum N y := by
  rw [harmonicSum, harmonicSum, harmonicSum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by rw [Pi.add_apply, add_div]

/-- Atomic tests are additive in the weights. -/
theorem atomicTest_add (N : ℕ) (x y : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N (x + y) g = atomicTest N x g + atomicTest N y g := by
  funext u
  simp only [atomicTest, Pi.add_apply, add_mul, sum_add_distrib]

/-- **A two-level combination of hyperplane tests is a hyperplane test**: if `x` (horizon `N`) and
`y` (horizon `2N`) lie on their harmonic hyperplanes, then `f = T_{log 2} f_x + f_y` is the atomic
test of `Sx + y` at horizon `2N`, on the hyperplane, and its Weil form is its Markov form. -/
theorem weilQuad_twoLevel_eq_markov {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} {x y : ℕ → ℝ}
    (hx : harmonicSum N x = 0) (hy : harmonicSum (2 * N) y = 0) :
    translate (Real.log 2) (atomicTest N x g) + atomicTest (2 * N) y g =
        atomicTest (2 * N) (dyadicShift x + y) g ∧
      weilQuad (atomicTest (2 * N) (dyadicShift x + y) g) =
        RHTower.markovEnergy (fun u => (atomicTest (2 * N) (dyadicShift x + y) g u : ℂ)) := by
  refine ⟨by rw [atomicTest_add, atomicTest_dyadicShift], ?_⟩
  have h : harmonicSum (2 * N) (dyadicShift x + y) = 0 := by
    rw [harmonicSum_add, harmonicSum_dyadicShift_eq_zero hx, hy, zero_add]
  exact weilQuad_atomicTest_eq_markov_of_harmonic hg hgsupp (2 * N) h

/-- **Multiresolution hyperplane positivity**: there is `G > 0` such that, eventually in `N`, for
hyperplane weights `x` (horizon `N`) and `y` (horizon `2N`), the two-level test
`T_{log 2} f_x + f_y` of a narrow atom satisfies the gap-paid bound at the finer horizon:
`W ≥ (φ₀ + c₀ G)‖·‖²`. No estimate of the coupling between the two levels is needed. -/
theorem exists_weilQuad_twoLevel_ge :
    ∃ G : ℝ, 0 < G ∧ ∀ {φ : ℝ → ℝ}, ContDiff ℝ 2 φ → (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) →
      0 < (∫ u, φ u ^ 2) → ∀ {K : ℝ}, (∀ u v, |φ u - φ v| ≤ K * |u - v|) →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing (2 * N) / 2 →
        w * ((2 * N : ℕ) : ℝ) ≤ RenormalizedArithmeticPotentialTheory.markovOverlapBound →
        0 ≤ defectFractionRetained ε w (2 * N) →
        ∀ x y : ℕ → ℝ, harmonicSum N x = 0 → harmonicSum (2 * N) y = 0 →
          (markovFinitePart φ ε w (2 * N) + defectFractionRetained ε w (2 * N) * G) *
              (∫ u, (translate (Real.log 2) (atomicTest N x (atomDilate φ w)) +
                atomicTest (2 * N) y (atomDilate φ w)) u ^ 2) ≤
            weilQuad (translate (Real.log 2) (atomicTest N x (atomDilate φ w)) +
              atomicTest (2 * N) y (atomDilate φ w)) := by
  obtain ⟨G, hG, hge⟩ := exists_weilQuad_atomicTest_ge_of_harmonic
  refine ⟨G, hG, fun {φ} hφ hφsupp hφ0 {K} hK {ε} hε hε1 => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hge hφ hφsupp hφ0 hK hε hε1
  refine ⟨N₀, fun N hN w hw0 hw hwN hc₀ x y hx hy => ?_⟩
  have hsum : translate (Real.log 2) (atomicTest N x (atomDilate φ w)) +
      atomicTest (2 * N) y (atomDilate φ w) =
        atomicTest (2 * N) (dyadicShift x + y) (atomDilate φ w) := by
    rw [atomicTest_add, atomicTest_dyadicShift]
  have h : harmonicSum (2 * N) (dyadicShift x + y) = 0 := by
    rw [harmonicSum_add, harmonicSum_dyadicShift_eq_zero hx, hy, zero_add]
  rw [hsum]
  exact hN₀ (2 * N) (by omega) w hw0 hw hwN hc₀ _ h

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
