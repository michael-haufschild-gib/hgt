import GaloisForLFunctions.RHTower.XiHeatSamplingBands
import GaloisForLFunctions.HTGeometry.VandermondeSamplingEnergy

/-!
# Arbitrarily many separated actual Xi heat sampling nodes

Multiplicative height bands at scales `4^i` give separated squared nodes at the
heat scale. Every finite number of such bands is simultaneously occupied at
all sufficiently small heat times. The Vandermonde determinant is uniformly
bounded away from zero while all nodes remain in a degree-dependent disk.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

def xiHeatSamplingRadius (N : ℕ) : ℝ := (3 * (4 : ℝ) ^ N) ^ 2 + 1

theorem xiHeatSamplingRadius_pos (N : ℕ) : 0 < xiHeatSamplingRadius N := by
  unfold xiHeatSamplingRadius
  positivity

/-- Every finite collection of actual scaled Xi nodes can be chosen uniformly separated. -/
theorem eventually_exists_xiHeat_finite_separated_nodes (N : ℕ) :
    ∀ᶠ τ : ℝ in atBot, ∃ q : Fin N → XiZeroCopy,
      let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
      (∀ i, ‖z i‖ ≤ xiHeatSamplingRadius N) ∧
        (∀ i j, i < j → 1 ≤ (z j).re - (z i).re) := by
  classical
  have hT : Tendsto (fun τ : ℝ => Real.exp (-τ / 2)) atBot atTop := by
    apply Real.tendsto_exp_atTop.comp
    convert tendsto_neg_atBot_atTop.atTop_mul_const (show (0 : ℝ) < 1 / 2 by positivity)
      using 1
    ext τ
    ring
  have hall : ∀ᶠ τ : ℝ in atBot, ∀ i : Fin N, ∃ q : XiZeroCopy,
      (4 : ℝ) ^ (i : ℕ) * Real.exp (-τ / 2) < (xiSpectralPoint q).re ∧
        (xiSpectralPoint q).re ≤ 3 * ((4 : ℝ) ^ (i : ℕ) * Real.exp (-τ / 2)) := by
    apply eventually_all.mpr
    intro i
    exact (hT.const_mul_atTop (show (0 : ℝ) < 4 ^ (i : ℕ) by positivity)).eventually
      eventually_exists_xiSpectralPoint_in_triple_band
  filter_upwards [hall, eventually_le_atBot (0 : ℝ)] with τ hall hτ
  choose q hqL hqU using hall
  let t := Real.exp τ
  let T := Real.exp (-τ / 2)
  let z := fun i : Fin N => (t : ℂ) * xiSpectralPoint (q i) ^ 2
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by simpa [t] using Real.exp_le_exp.mpr hτ
  have hT0 : 0 < T := Real.exp_pos _
  have htT : t * T ^ 2 = 1 := by
    dsimp [t, T]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hscale (x : ℝ) : t * (x * T) ^ 2 = x ^ 2 := by
    calc _ = x ^ 2 * (t * T ^ 2) := by ring
         _ = _ := by rw [htT, mul_one]
  have hb (i : Fin N) :
      ((4 : ℝ) ^ (i : ℕ)) ^ 2 - 1 ≤ (z i).re ∧
      (z i).re ≤ (3 * (4 : ℝ) ^ (i : ℕ)) ^ 2 ∧
      ‖z i‖ ≤ (3 * (4 : ℝ) ^ (i : ℕ)) ^ 2 + 1 := by
    have hs : (xiSpectralPoint (q i)).im ^ 2 < 1 / 4 := by
      have him : (xiSpectralPoint (q i)).im = -(((q i).1 : ℂ).re - 1 / 2) := by
        simp [xiSpectralPoint]
      rw [him, neg_sq]
      exact xi_divisor_support_centered_re_sq_lt_quarter (q i).1
    have hreal0 : 0 ≤ (xiSpectralPoint (q i)).re := by
      exact (show 0 ≤ (4 : ℝ) ^ (i : ℕ) * Real.exp (-τ / 2) by positivity).trans (hqL i).le
    have hlow := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by positivity) hreal0).2 (hqL i).le) ht.le
    have hu : (xiSpectralPoint (q i)).re ≤ (3 * (4 : ℝ) ^ (i : ℕ)) * T := by
      dsimp [T]
      linarith [hqU i]
    have hupp := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hreal0 (by positivity)).2 hu) ht.le
    change t * ((4 : ℝ) ^ (i : ℕ) * T) ^ 2 ≤ _ at hlow
    rw [hscale] at hlow hupp
    have him0 := mul_nonneg ht.le (sq_nonneg (xiSpectralPoint (q i)).im)
    have him1 : t * (xiSpectralPoint (q i)).im ^ 2 ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hs.le ht.le
      nlinarith
    have hre : (z i).re =
        t * ((xiSpectralPoint (q i)).re ^ 2 - (xiSpectralPoint (q i)).im ^ 2) := by
      simp [z, pow_two, Complex.mul_re]
    have hn : ‖z i‖ =
        t * ((xiSpectralPoint (q i)).re ^ 2 + (xiSpectralPoint (q i)).im ^ 2) := by
      dsimp only [z]
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hre, hn]
    constructor
    · nlinarith
    constructor <;> nlinarith
  refine ⟨q, ?_⟩
  change (∀ i, ‖z i‖ ≤ xiHeatSamplingRadius N) ∧ _
  constructor
  · intro i
    refine (hb i).2.2.trans ?_
    unfold xiHeatSamplingRadius
    have hpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 4 by linarith) i.isLt.le
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2
      (mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 3 by positivity))
    linarith
  · intro i j hij
    have hp : (4 : ℝ) ^ ((i : ℕ) + 1) ≤ (4 : ℝ) ^ (j : ℕ) :=
      pow_le_pow_right₀ (by linarith) (Nat.succ_le_iff.mpr hij)
    rw [pow_succ] at hp
    have hp2 := (sq_le_sq₀ (by positivity) (by positivity)).2 hp
    have hone : 1 ≤ (4 : ℝ) ^ (i : ℕ) := one_le_pow₀ (by linarith)
    have hone2 : 1 ≤ ((4 : ℝ) ^ (i : ℕ)) ^ 2 := by nlinarith
    have hL := (hb j).1
    have hU := (hb i).2.1
    nlinarith

/-- The full sampling determinant has one lower bound at every finite order. -/
theorem eventually_exists_xiHeat_sampling_determinant (N : ℕ) :
    ∀ᶠ τ : ℝ in atBot, ∃ q : Fin N → XiZeroCopy,
      let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
      (∀ i, ‖z i‖ ≤ xiHeatSamplingRadius N) ∧ 1 ≤ ‖(Matrix.vandermonde z).det‖ := by
  filter_upwards [eventually_exists_xiHeat_finite_separated_nodes N] with τ hτ
  obtain ⟨q, hq, hgap⟩ := hτ
  refine ⟨q, hq, ?_⟩
  rw [Matrix.det_vandermonde, norm_prod]
  apply Finset.one_le_prod
  intro i _
  rw [norm_prod]
  apply Finset.one_le_prod
  intro j hj
  have h := hgap i j (Finset.mem_Ioi.mp hj)
  exact h.trans (by simpa only [Complex.sub_re] using (Complex.re_le_norm
    ((Real.exp τ : ℂ) * xiSpectralPoint (q j) ^ 2 -
      (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2)))

end
end RHTower
