import GaloisForLFunctions.RHTower.WeilProducerReciprocalZetaAtomOrder
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound

/-!
# Polynomial reciprocal prefixes retain the full boundary atom order

At every fixed ordinate, the logarithmic radial order of the complete remainder
is the mass of the original Weil boundary atom, uniformly over all prefixes of
any fixed polynomial length. Ordinary reciprocal convergence makes those
prefixes subpower; the existing source atom-order law supplies the exponent.

The ordinate is fixed before the radial limit. This gives no moving-height
uniformity, atomicity, integer atom mass, or settled phase.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.RHTower

namespace RHTower.WeilWorkSettledPhase
open WeilSpectral WeilHerglotz

noncomputable section

/-- The first `N` terms of the original source reciprocal, on the radial line
through the fixed boundary ordinate `a`. -/
def reciprocalPrefix (lam : ℕ → ℝ) (a h : ℝ) (N : ℕ) : ℂ :=
  dirichletPartialSum
    (fun n => producerMobius (fun n => if 2 ≤ n then lam n else 0) (n + 1)) N
    (((1 / 2 + h : ℝ) : ℂ) + a * I)

private theorem log_inverse_tendsto :
    Tendsto (fun h : ℝ => Real.log (1 / h)) (𝓝[>] 0) atTop := by
  refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun h => ?_
  simp [one_div, Real.log_inv]

private theorem prefix_power_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ δ → ∀ N : ℕ,
      ‖reciprocalPrefix lam a h N‖ ≤ C * ((N : ℝ) + 1) ^ δ := by
  let c : ℕ → ℂ := fun n => producerMobius (fun n => if 2 ≤ n then lam n else 0) (n + 1)
  let s : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + a * I
  have hs : 1 / 2 < s.re := by
    simpa [s] using (show (1 : ℝ) / 2 < 1 / 2 + δ by linarith)
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp
    ((WeilSingularArithmetic.reciprocal_dirichletConvergesAt hW hs).choose_spec.cauchySeq.isBounded_range)
  have hKb : ∀ N, ‖dirichletPartialSum c N s‖ ≤ K :=
    fun N => hK _ (mem_range_self N)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hKb 0)
  refine ⟨2 * K, by positivity, fun h hh hhδ N => ?_⟩
  let f : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (δ - h)
  let g : ℕ → ℂ := fun n => c n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
  have hf : ∀ n, 0 ≤ f n := fun n => Real.rpow_nonneg (by positivity) _
  have hmono : Monotone f := by
    intro n m hnm
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      (sub_nonneg.mpr hhδ)
  have hvar : (∑ i ∈ Finset.range (N - 1), |f (i + 1) - f i|) = f (N - 1) - f 0 := by
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ _)))]
    exact Finset.sum_range_sub f (N - 1)
  have hsum : reciprocalPrefix lam a h N =
      ∑ i ∈ Finset.range N, (f i : ℂ) * g i := by
    unfold reciprocalPrefix dirichletPartialSum
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f, g, c]
    rw [Complex.ofReal_cpow (by positivity)]
    have hn : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
    rw [mul_left_comm, ← Complex.cpow_add _ _ hn]
    congr 2
    dsimp [s]
    push_cast
    ring
  have hb := RHTower.norm_sum_ofReal_mul_le_of_bounded_partial
    (g := g) (f := f) (C := K) (fun k => hKb k) hf N
  rw [hvar] at hb
  have hweight : f (N - 1) ≤ ((N : ℝ) + 1) ^ δ := by
    exact (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (Nat.sub_le N 1) 1)
      (sub_nonneg.mpr hhδ)).trans
      (Real.rpow_le_rpow_of_exponent_le (by have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) (by linarith))
  rw [hsum]
  calc
    _ ≤ (f (N - 1) + (f (N - 1) - f 0)) * K := hb
    _ ≤ (2 * K) * ((N : ℝ) + 1) ^ δ := by nlinarith [hf 0]

/-- At each fixed ordinate, reciprocal prefixes of any fixed polynomial length
have uniformly subpower radial growth. Full positivity supplies convergence. -/
theorem reciprocalPrefix_log_order_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a : ℝ) {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ N : ℕ, (N : ℝ) ≤ h ^ (-A) →
      Real.log (1 + ‖reciprocalPrefix lam a h N‖) / Real.log (1 / h) < ε := by
  let δ : ℝ := ε / (2 * (A + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : A * δ < ε / 2 := by
    have he : (2 * (A + 1)) * δ = ε := by
      dsimp [δ]
      field_simp
    nlinarith
  obtain ⟨C, hC, hb⟩ := prefix_power_bound hW a hδ
  let D : ℝ := Real.log (1 + C) + δ * Real.log 2
  have hDlim : Tendsto (fun h : ℝ => D / Real.log (1 / h)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_inverse_tendsto
  filter_upwards [Ioo_mem_nhdsGT hδ, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
    hDlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))] with h hhδ hh hD
  intro N hN
  have hL : 0 < Real.log (1 / h) := Real.log_pos ((one_lt_div hh.1).mpr hh.2)
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have hnpow : 1 ≤ ((N : ℝ) + 1) ^ δ := Real.one_le_rpow (by have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hδ.le
  have hplog : Real.log (1 + ‖reciprocalPrefix lam a h N‖) ≤
      Real.log (1 + C) + δ * Real.log ((N : ℝ) + 1) := by
    calc
      _ ≤ Real.log ((1 + C) * ((N : ℝ) + 1) ^ δ) := by
        apply Real.log_le_log (by positivity)
        nlinarith [hb h hh.1 hhδ.2.le N]
      _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hn]
  have hhp : 1 ≤ h ^ (-A) := by
    have h' := Real.rpow_le_rpow_of_exponent_ge hh.1 hh.2.le (neg_nonpos.mpr hA)
    simpa using h'
  have hnle : (N : ℝ) + 1 ≤ 2 * h ^ (-A) := by linarith
  have hnlog : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + A * Real.log (1 / h) := by
    calc
      _ ≤ Real.log (2 * h ^ (-A)) := Real.log_le_log hn hnle
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hh.1]
                  simp only [one_div, Real.log_inv]; ring
  have htotal : Real.log (1 + ‖reciprocalPrefix lam a h N‖) ≤
      D + (A * δ) * Real.log (1 / h) := by dsimp [D]; nlinarith
  calc
    _ ≤ (D + (A * δ) * Real.log (1 / h)) / Real.log (1 / h) :=
      div_le_div_of_nonneg_right htotal hL.le
    _ = D / Real.log (1 / h) + A * δ := by field_simp
    _ < ε := by linarith

private theorem log_one_add_norm_bounds (z : ℂ) :
    max 0 (Real.log ‖z‖) ≤ Real.log (1 + ‖z‖) ∧
    Real.log (1 + ‖z‖) ≤ Real.log 2 + max 0 (Real.log ‖z‖) := by
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hn : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  constructor
  · refine max_le hn ?_
    by_cases hz : z = 0
    · simp [hz]
    · exact Real.log_le_log (norm_pos_iff.mpr hz) (by linarith [norm_nonneg z])
  · by_cases hz : ‖z‖ ≤ 1
    · exact (Real.log_le_log hp (by linarith)).trans (le_add_of_nonneg_right (le_max_left _ _))
    · have hzpos : 0 < ‖z‖ := by linarith
      calc
        Real.log (1 + ‖z‖) ≤ Real.log (2 * ‖z‖) := Real.log_le_log hp (by linarith)
        _ = Real.log 2 + Real.log ‖z‖ := Real.log_mul (by norm_num) (ne_of_gt hzpos)
        _ ≤ Real.log 2 + max 0 (Real.log ‖z‖) := add_le_add le_rfl (le_max_right _ _)

private theorem log_remainder_distance (z p : ℂ) :
    |Real.log (1 + ‖z - p‖) - Real.log (1 + ‖z‖)| ≤ Real.log (1 + ‖p‖) := by
  have hbound (u v : ℂ) : Real.log (1 + ‖u + v‖) ≤
      Real.log (1 + ‖u‖) + Real.log (1 + ‖v‖) := by
    rw [← Real.log_mul (by positivity : 1 + ‖u‖ ≠ 0) (by positivity : 1 + ‖v‖ ≠ 0)]
    apply Real.log_le_log (by positivity)
    nlinarith [norm_add_le u v, norm_nonneg u, norm_nonneg v]
  apply abs_sub_le_iff.mpr
  constructor
  · have h := hbound z (-p)
    simp only [norm_neg, ← sub_eq_add_neg] at h
    linarith
  · have h := hbound (z - p) p
    rw [sub_add_cancel] at h
    linarith

private theorem log_one_add_norm_tendsto {g : ℝ → ℂ} {m : ℝ} (hm : 0 ≤ m)
    (hg : Tendsto (fun h => Real.log ‖g h‖ / Real.log (1 / h))
      (𝓝[>] 0) (𝓝 m)) :
    Tendsto (fun h => Real.log (1 + ‖g h‖) / Real.log (1 / h))
      (𝓝[>] 0) (𝓝 m) := by
  have hmax : Tendsto (fun h => max 0 (Real.log ‖g h‖ / Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 m) := by
    simpa only [max_eq_right hm] using (tendsto_const_nhds (x := (0 : ℝ))).max hg
  have hc : Tendsto (fun h : ℝ => Real.log 2 / Real.log (1 / h))
      (𝓝[>] 0) (𝓝 0) := log_inverse_tendsto.const_div_atTop _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmax
    (by simpa only [zero_add] using hc.add hmax)
  · filter_upwards [log_inverse_tendsto.eventually (eventually_gt_atTop 0)] with h hL
    have h := div_le_div_of_nonneg_right (log_one_add_norm_bounds (g h)).1 hL.le
    rwa [← max_div_div_right hL.le, zero_div] at h
  · filter_upwards [log_inverse_tendsto.eventually (eventually_gt_atTop 0)] with h hL
    have h := div_le_div_of_nonneg_right (log_one_add_norm_bounds (g h)).2 hL.le
    rwa [add_div, ← max_div_div_right hL.le, zero_div] at h

/-- Every polynomial-length reciprocal prefix leaves a remainder with exactly
the full original boundary atom exponent. Full positivity is the sole source
premise; the conclusion includes zero atoms and is uniform in prefix length.
The boundary ordinate and polynomial exponent are fixed before the limit. -/
theorem exists_reciprocal_polynomial_tail_atom_order {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ (a : ℝ) (A : ℝ), 0 ≤ A → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ N : ℕ, (N : ℝ) ≤ h ^ (-A) →
          |Real.log (1 + ‖G (((1 / 2 + h : ℝ) : ℂ) + a * I) -
              reciprocalPrefix lam a h N‖) / Real.log (1 / h) -
            (boundaryMeasure hW).real {a}| < ε := by
  obtain ⟨G, hGd, hGr, hGlim⟩ := tendsto_log_norm_reciprocalZeta_div_log hW
  refine ⟨G, hGd, hGr, fun a A hA ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by positivity
  have hlim := log_one_add_norm_tendsto measureReal_nonneg (hGlim a)
  have hnear := (Metric.tendsto_nhds.mp hlim) (ε / 2) hε2
  filter_upwards [hnear, reciprocalPrefix_log_order_zero hW a hA hε2,
    log_inverse_tendsto.eventually (eventually_gt_atTop 0)] with h hG hP hL
  intro N hN
  rw [Real.dist_eq] at hG
  have hdiff := div_le_div_of_nonneg_right
    (log_remainder_distance (G (((1 / 2 + h : ℝ) : ℂ) + a * I))
      (reciprocalPrefix lam a h N)) hL.le
  have hdiff' : |Real.log (1 + ‖G (((1 / 2 + h : ℝ) : ℂ) + a * I) -
      reciprocalPrefix lam a h N‖) / Real.log (1 / h) -
      Real.log (1 + ‖G (((1 / 2 + h : ℝ) : ℂ) + a * I)‖) / Real.log (1 / h)|
      < ε / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hL]
    exact hdiff.trans_lt (hP N hN)
  have ht := abs_sub_le
    (Real.log (1 + ‖G (((1 / 2 + h : ℝ) : ℂ) + a * I) - reciprocalPrefix lam a h N‖) /
      Real.log (1 / h))
    (Real.log (1 + ‖G (((1 / 2 + h : ℝ) : ℂ) + a * I)‖) / Real.log (1 / h))
    ((boundaryMeasure hW).real {a})
  linarith

end
end RHTower.WeilWorkSettledPhase
