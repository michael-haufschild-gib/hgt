import GaloisForLFunctions.RHTower.XiHeatFiniteSamplingBands
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower

/-!
# Actual Xi samples in a disk of quadratic degree radius

Fixed-width zero-counting windows supply one actual divisor copy near each
height (i+1)T. At the heat scale t*T²=1, these squared nodes are uniformly
separated and lie in a disk whose radius grows quadratically with the order.
The same heat cutoff works simultaneously at every finite order.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

/-- Actual divisor copies occupy every sufficiently high fixed-width window. -/
theorem exists_xiSpectralPoint_in_bounded_windows :
    ∃ h : ℝ, 0 < h ∧ ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ q : XiZeroCopy, T - h < (xiSpectralPoint q).re ∧ (xiSpectralPoint q).re ≤ T + h := by
  classical
  obtain ⟨h, hh, T₁, hT₁, hwin⟩ := exists_xiZeroCount_window_ge_log
  refine ⟨h, hh, max T₁ (2 * h + 4), ?_, ?_⟩
  · exact (show 0 < T₁ by linarith only [hT₁]).trans_le (le_max_left _ _)
  intro T hT
  have hbase : T₁ ≤ T := (le_max_left _ _).trans hT
  have hwidth : 2 * h + 4 ≤ T := (le_max_right _ _).trans hT
  have hlo : 0 ≤ T - h := by linarith only [hwidth, hh]
  have hhi : 0 ≤ T + h := by linarith only [hwidth, hh]
  have hlog : 0 < Real.log T := Real.log_pos (by linarith only [hwidth, hh])
  have hcount : (xiZeroCount (T - h) : ℝ) < (xiZeroCount (T + h) : ℝ) := by
    linarith only [hwin T hbase, hlog]
  have hnot : ¬ xiSupportsPos (T + h) ⊆ xiSupportsPos (T - h) := by
    intro hsub
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun ρ => (xiSupportMultiplicity ρ : ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
    have eL := congrArg (fun n : ℤ => (n : ℝ)) (xiZeroCount_eq_pos_sum hlo)
    have eU := congrArg (fun n : ℤ => (n : ℝ)) (xiZeroCount_eq_pos_sum hhi)
    push_cast at eL eU
    rw [← eL, ← eU] at hle
    exact (not_le_of_gt hcount) hle
  obtain ⟨ρ, hρ, hρnot⟩ := Finset.not_subset.mp hnot
  have hρmem := mem_xiSupportsPos.mp hρ
  have hupper : (ρ : ℂ).im ≤ T + h := by
    simpa only [abs_of_pos hρmem.2] using hρmem.1
  have hlower : T - h < (ρ : ℂ).im := by
    by_contra hbad
    apply hρnot
    rw [mem_xiSupportsPos]
    exact ⟨by rw [abs_of_pos hρmem.2]; exact le_of_not_gt hbad, hρmem.2⟩
  have hm : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have := xi_divisor_pos_on_support ρ
    omega
  refine ⟨⟨ρ, ⟨0, hm⟩⟩, ?_⟩
  simpa only [xiSpectralPoint_re_eq] using And.intro hlower hupper

def xiHeatQuadraticSamplingRadius (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ 2 + 1

theorem xiHeatQuadraticSamplingRadius_pos (N : ℕ) :
    0 < xiHeatQuadraticSamplingRadius N := by
  unfold xiHeatQuadraticSamplingRadius
  positivity

/-- One cutoff supplies every finite order in a disk of quadratic, rather than exponential, radius. -/
theorem eventually_forall_exists_xiHeat_quadratic_separated_nodes :
    ∀ᶠ τ : ℝ in atBot, ∀ N : ℕ, ∃ q : Fin N → XiZeroCopy,
      let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
      (∀ i, ‖z i‖ ≤ xiHeatQuadraticSamplingRadius N) ∧
        (∀ i j, i < j → 1 ≤ (z j).re - (z i).re) := by
  classical
  obtain ⟨h, hh, T₀, _hT₀, hwin⟩ := exists_xiSpectralPoint_in_bounded_windows
  have hT : Tendsto (fun τ : ℝ => Real.exp (-τ / 2)) atBot atTop := by
    apply Real.tendsto_exp_atTop.comp
    convert tendsto_neg_atBot_atTop.atTop_mul_const (show (0 : ℝ) < 1 / 2 by positivity)
      using 1
    ext τ
    ring
  have hall : ∀ᶠ τ : ℝ in atBot, ∀ i : ℕ, ∃ q : XiZeroCopy,
      ((i : ℝ) + 1) * Real.exp (-τ / 2) - h < (xiSpectralPoint q).re ∧
        (xiSpectralPoint q).re ≤ ((i : ℝ) + 1) * Real.exp (-τ / 2) + h := by
    filter_upwards [hT.eventually (eventually_ge_atTop T₀)] with τ hτ i
    apply hwin
    exact hτ.trans (le_mul_of_one_le_left (Real.exp_pos _).le (by
      have hi := Nat.cast_nonneg (α := ℝ) i
      linarith only [hi]))
  filter_upwards [hall, hT.eventually (eventually_ge_atTop (4 * h)),
    eventually_le_atBot (0 : ℝ)] with τ hall hwidth hτ N
  choose q hqL hqU using fun i : Fin N => hall (i : ℕ)
  let t := Real.exp τ
  let T := Real.exp (-τ / 2)
  let z := fun i : Fin N => (t : ℂ) * xiSpectralPoint (q i) ^ 2
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by simpa [t] using Real.exp_le_exp.mpr hτ
  have hT0 : 0 < T := Real.exp_pos _
  have hwidth' : h ≤ T / 4 := by dsimp [T]; linarith only [hwidth]
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
      (((i : ℕ) : ℝ) + 3 / 4) ^ 2 - 1 / 4 ≤ (z i).re ∧
      (z i).re ≤ (((i : ℕ) : ℝ) + 5 / 4) ^ 2 ∧
      ‖z i‖ ≤ (((i : ℕ) : ℝ) + 5 / 4) ^ 2 + 1 / 4 := by
    have hi := Nat.cast_nonneg (α := ℝ) (i : ℕ)
    have hl : (((i : ℕ) : ℝ) + 3 / 4) * T ≤ (xiSpectralPoint (q i)).re := by
      have hq := hqL i
      change (((i : ℕ) : ℝ) + 1) * T - h < _ at hq
      nlinarith only [hq, hwidth']
    have hu : (xiSpectralPoint (q i)).re ≤ (((i : ℕ) : ℝ) + 5 / 4) * T := by
      have hq := hqU i
      change _ ≤ (((i : ℕ) : ℝ) + 1) * T + h at hq
      nlinarith only [hq, hwidth']
    have hr : 0 ≤ (xiSpectralPoint (q i)).re :=
      (show 0 ≤ (((i : ℕ) : ℝ) + 3 / 4) * T by positivity).trans hl
    have hlow := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) hr).2 hl) ht.le
    have hupp := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hr (by positivity)).2 hu) ht.le
    rw [hscale] at hlow hupp
    have hs : (xiSpectralPoint (q i)).im ^ 2 < 1 / 4 := by
      have him : (xiSpectralPoint (q i)).im = -(((q i).1 : ℂ).re - 1 / 2) := by
        simp [xiSpectralPoint]
      rw [him, neg_sq]
      exact xi_divisor_support_centered_re_sq_lt_quarter (q i).1
    have him0 := mul_nonneg ht.le (sq_nonneg (xiSpectralPoint (q i)).im)
    have him1 : t * (xiSpectralPoint (q i)).im ^ 2 ≤ 1 / 4 := by
      have hm := mul_le_mul_of_nonneg_left hs.le ht.le
      nlinarith only [hm, ht1]
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
    · nlinarith only [hlow, him1]
    constructor
    · nlinarith only [hupp, him0]
    · nlinarith only [hupp, him1]
  refine ⟨q, ?_⟩
  change (∀ i, ‖z i‖ ≤ xiHeatQuadraticSamplingRadius N) ∧ _
  constructor
  · intro i
    refine (hb i).2.2.trans ?_
    have hiN : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hs := (sq_le_sq₀
      (show 0 ≤ ((i : ℕ) : ℝ) + 5 / 4 by positivity)
      (show 0 ≤ (N : ℝ) + 1 by positivity)).2
      (show ((i : ℕ) : ℝ) + 5 / 4 ≤ (N : ℝ) + 1 by linarith only [hiN])
    unfold xiHeatQuadraticSamplingRadius
    linarith only [hs]
  · intro i j hij
    have hi := Nat.cast_nonneg (α := ℝ) (i : ℕ)
    have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hij
    have hs := (sq_le_sq₀
      (show 0 ≤ ((i : ℕ) : ℝ) + 7 / 4 by positivity)
      (show 0 ≤ ((j : ℕ) : ℝ) + 3 / 4 by positivity)).2
      (show ((i : ℕ) : ℝ) + 7 / 4 ≤ ((j : ℕ) : ℝ) + 3 / 4 by linarith only [hij'])
    nlinarith only [hs, (hb j).1, (hb i).2.1, hi]

/-- Determinant control with quadratic sampling radius, uniform over all orders. -/
theorem eventually_forall_exists_xiHeat_quadratic_sampling_determinant :
    ∀ᶠ τ : ℝ in atBot, ∀ N : ℕ, ∃ q : Fin N → XiZeroCopy,
      let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
      (∀ i, ‖z i‖ ≤ xiHeatQuadraticSamplingRadius N) ∧ 1 ≤ ‖(Matrix.vandermonde z).det‖ := by
  filter_upwards [eventually_forall_exists_xiHeat_quadratic_separated_nodes] with τ hτ N
  obtain ⟨q, hq, hgap⟩ := hτ N
  refine ⟨q, hq, ?_⟩
  rw [Matrix.det_vandermonde, norm_prod]
  apply Finset.one_le_prod
  intro i _
  rw [norm_prod]
  apply Finset.one_le_prod
  intro j hj
  apply (hgap i j (Finset.mem_Ioi.mp hj)).trans
  rw [← Complex.sub_re]
  exact Complex.re_le_norm _

end
end RHTower
