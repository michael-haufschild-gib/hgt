import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint
import GaloisForLFunctions.RHTower.FloorTransformHarmonicInverse

/-!
# A paid receiver bounds the Dirichlet series up to its abscissa

Let `1/2 < a < 1` and let `Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`. If every pronic energy of `c`
is at most `E`, the general pole law of the Mellin pairing `Σ_n A(n) Δ_n(σ) = ζ(σ)(C(σ) − m)` gives,
uniformly on `a < σ < 1`,

`|C(σ) − m| ≤ √E √(2(1 + 1/(2a − 1)))`,  `C(σ) = Σ_d c(d) d^{-σ}`

(`abs_dirichletSeries_sub_mean_le_of_abscissa`). A weight whose Dirichlet series blows up as
`σ ↓ a` is therefore never paid (`not_receiverBounded_of_tendsto_abs_dirichletSeries`); on the
damped class `𝒞(K, ε)`, `0 < ε < 1/2`, the abscissa is `a = 1 − ε`.

**Convolutions.** For `(k ⋆ q)(n) = Σ_{j ∣ n} k(j) q(n/j)` the Dirichlet series factor,
`Σ (k ⋆ q)(n) n^{-σ} = K(σ) Q(σ)` (`hasSum_dirichletConv_mul_rpow`). If `q ≥ 0` lies in `𝒞(K, ε)`
with `Σ q(d) d^{-(1−ε)} = ∞`, and `Σ |k(j)| j^{-(1−ε)} < ∞` with `K(1 − ε) ≠ 0`, then `K(σ) → K(1−ε)`
and `Q(σ) → ∞` as `σ ↓ 1 − ε`, so `k ⋆ q` is not paid
(`not_receiverBounded_dirichletConv_of_not_summable`). Against
`not_receiverBounded_dirichletConv_of_drift_critical` (for `ε < 1/2`): the kernel needs absolute
convergence only at the abscissa `1 − ε` instead of at the critical point `1/2`, and the drift
`n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}` is replaced by divergence of `Q` at the abscissa, which it implies.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The uniform pole law -/

/-- The pole-law factor is uniform away from the critical point:
`((1 − σ)/σ) √(2σ²(1 + 1/(2σ − 1))) ≤ √(2(1 + 1/(2a − 1)))` for `1/2 < a < σ < 1`. -/
theorem poleLawFactor_le {a σ : ℝ} (ha : 1 / 2 < a) (haσ : a < σ) (hσ1 : σ < 1) :
    (1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) ≤
      Real.sqrt (2 * (1 + 1 / (2 * a - 1))) := by
  have hσ0 : 0 < σ := by linarith
  have h2a : 0 < 2 * a - 1 := by linarith
  have h2σ : 0 < 2 * σ - 1 := by linarith
  have hfac : (1 - σ) / σ ≤ 1 := by rw [div_le_one hσ0]; linarith
  have hinv : 1 / (2 * σ - 1) ≤ 1 / (2 * a - 1) := one_div_le_one_div_of_le h2a (by linarith)
  have hinv0 : 0 ≤ 1 / (2 * σ - 1) := (one_div_pos.mpr h2σ).le
  have hsq : σ ^ 2 ≤ 1 := by nlinarith
  have hin : 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) ≤ 2 * (1 + 1 / (2 * a - 1)) := by
    have := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 1 + 1 / (2 * σ - 1) by linarith)
    nlinarith
  calc (1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))
      ≤ 1 * Real.sqrt (2 * (1 + 1 / (2 * a - 1))) :=
        mul_le_mul hfac (Real.sqrt_le_sqrt hin) (Real.sqrt_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **A paid receiver bounds the Dirichlet series up to its abscissa.** Let `1/2 < a` and
`Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`. If every pronic energy of `c` is at most `E`, then
`|C(σ) − m| ≤ √E √(2(1 + 1/(2a − 1)))` for all `a < σ < 1`. -/
theorem abs_dirichletSeries_sub_mean_le_of_abscissa {E a σ : ℝ} {c : ℕ → ℝ} (ha : 1 / 2 < a)
    (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) (haσ : a < σ) (hσ1 : σ < 1) :
    |(∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d| ≤
      Real.sqrt E * Real.sqrt (2 * (1 + 1 / (2 * a - 1))) := by
  have h := abs_dirichletSeries_sub_mean_le_of_energy_of_summable (θ := (a + σ) / 2)
    (by linarith) (by linarith) (by linarith) hσ1 (hc _ (by linarith)) hE
  calc _ ≤ _ := h
    _ = Real.sqrt E * ((1 - σ) / σ * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (poleLawFactor_le ha haσ hσ1) (Real.sqrt_nonneg E)

/-- **A Dirichlet series blowing up at its abscissa is never paid.** Let `1/2 < a < 1` and
`Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`. If `|C(σ)| → ∞` as `σ ↓ a`, the receiver of `c` is
unbounded. -/
theorem not_receiverBounded_of_tendsto_abs_dirichletSeries {a : ℝ} {c : ℕ → ℝ} (ha : 1 / 2 < a)
    (ha1 : a < 1) (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hC : Tendsto (fun σ : ℝ => |∑' d : ℕ, c d * (d : ℝ) ^ (-σ)|) (𝓝[>] a) atTop) :
    ¬ ReceiverBounded c := by
  rintro ⟨E, hE⟩
  set M := |∑' d : ℕ, c d / d| + Real.sqrt E * Real.sqrt (2 * (1 + 1 / (2 * a - 1)))
  obtain ⟨σ, hσM, hσ⟩ := ((hC.eventually_gt_atTop M).and (Ioo_mem_nhdsGT ha1)).exists
  have h := abs_dirichletSeries_sub_mean_le_of_abscissa ha hc hE hσ.1 hσ.2
  have htri := abs_sub_abs_le_abs_sub (∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) (∑' d : ℕ, c d / d)
  linarith

/-- **The pole law below half damping.** For `0 < ε < 1/2`, a weight of `𝒞(K, ε)` whose Dirichlet
series satisfies `|C(σ)| → ∞` as `σ ↓ 1 − ε` has unbounded receiver. -/
theorem not_receiverBounded_of_tendsto_abs_dirichletSeries_dampedClass {K ε : ℝ} {c : ℕ → ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hc : DampedClass K ε c)
    (hC : Tendsto (fun σ : ℝ => |∑' d : ℕ, c d * (d : ℝ) ^ (-σ)|) (𝓝[>] (1 - ε)) atTop) :
    ¬ ReceiverBounded c :=
  not_receiverBounded_of_tendsto_abs_dirichletSeries (by linarith) (by linarith)
    (fun _ hθ => summable_abs_mul_rpow_of_dampedClass hε hc hθ) hC

/-! ### Dirichlet series at the abscissa -/

/-- Each term `x j^{-σ}` is right-continuous in `σ` at `a > 0` (the term `j = 0` vanishes). -/
theorem tendsto_mul_rpow_neg_nhdsGT {a : ℝ} (ha : 0 < a) (x : ℝ) (j : ℕ) :
    Tendsto (fun σ : ℝ => x * (j : ℝ) ^ (-σ)) (𝓝[>] a) (𝓝 (x * (j : ℝ) ^ (-a))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : ∀ τ : ℝ, 0 < τ → x * ((0 : ℕ) : ℝ) ^ (-τ) = 0 := fun τ hτ => by
      rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hτ.ne'), mul_zero]
    rw [h0 a ha]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (h0 σ (ha.trans hσ)).symm
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    exact (((continuous_const.rpow continuous_neg fun _ => Or.inl hj0.ne').tendsto a).const_mul
      x).mono_left nhdsWithin_le_nhds

/-- `j^{-σ} ≤ j^{-a}` for `0 < a ≤ σ`, including `j = 0`. -/
theorem rpow_neg_le_of_le {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) (j : ℕ) :
    (j : ℝ) ^ (-σ) ≤ (j : ℝ) ^ (-a) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (ha.trans_le haσ).ne'),
      Real.zero_rpow (neg_ne_zero.mpr ha.ne')]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)

/-- A Dirichlet series absolutely convergent at `a > 0` is right-continuous at `a`
(dominated convergence). -/
theorem tendsto_dirichletSeries_nhdsGT {k : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-a))) :
    Tendsto (fun σ : ℝ => ∑' j : ℕ, k j * (j : ℝ) ^ (-σ)) (𝓝[>] a)
      (𝓝 (∑' j : ℕ, k j * (j : ℝ) ^ (-a))) := by
  refine tendsto_tsum_of_dominated_convergence (f := fun σ j => k j * (j : ℝ) ^ (-σ)) hk
    (fun j => tendsto_mul_rpow_neg_nhdsGT ha (k j) j) ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
  exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_le ha (le_of_lt hσ) j) (abs_nonneg _)

/-- A nonnegative Dirichlet series divergent at `a > 0` tends to `+∞` as `σ ↓ a`. -/
theorem tendsto_dirichletSeries_atTop_of_not_summable {q : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hq : ∀ d, 0 ≤ q d) (hsum : ∀ σ, a < σ → Summable (fun d : ℕ => q d * (d : ℝ) ^ (-σ)))
    (hdiv : ¬ Summable (fun d : ℕ => q d * (d : ℝ) ^ (-a))) :
    Tendsto (fun σ : ℝ => ∑' d : ℕ, q d * (d : ℝ) ^ (-σ)) (𝓝[>] a) atTop := by
  have hnn : ∀ (τ : ℝ) (d : ℕ), 0 ≤ q d * (d : ℝ) ^ (-τ) := fun τ d =>
    mul_nonneg (hq d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hpart : Tendsto (fun N : ℕ => ∑ d ∈ range N, q d * (d : ℝ) ^ (-a)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (hnn a)).mp hdiv
  rw [tendsto_atTop]
  intro M
  obtain ⟨N, hN⟩ := (hpart.eventually_gt_atTop M).exists
  have hcont : Tendsto (fun σ : ℝ => ∑ d ∈ range N, q d * (d : ℝ) ^ (-σ)) (𝓝[>] a)
      (𝓝 (∑ d ∈ range N, q d * (d : ℝ) ^ (-a))) :=
    tendsto_finsetSum _ fun d _ => tendsto_mul_rpow_neg_nhdsGT ha (q d) d
  filter_upwards [hcont.eventually (lt_mem_nhds hN), self_mem_nhdsWithin] with σ h1 h2
  exact h1.le.trans ((hsum σ h2).sum_le_tsum _ fun d _ => hnn σ d)

/-! ### Convolutions -/

/-- **The product law** `Σ (k ⋆ q)(n) n^{-σ} = K(σ) Q(σ)` for absolutely convergent series. -/
theorem hasSum_dirichletConv_mul_rpow {k q : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-σ)))
    (hq : Summable (fun d : ℕ => |q d| * (d : ℝ) ^ (-σ))) :
    HasSum (fun n : ℕ => RHTower.dirichletConv k q n * (n : ℝ) ^ (-σ))
      ((∑' j : ℕ, k j * (j : ℝ) ^ (-σ)) * ∑' d : ℕ, q d * (d : ℝ) ^ (-σ)) := by
  have hnorm : ∀ (x : ℝ) (j : ℕ), |x| * (j : ℝ) ^ (-σ) = ‖x * (j : ℝ) ^ (-σ)‖ := fun x j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
  have hk' := hk.congr fun j => hnorm (k j) j
  have hq' := hq.congr fun d => hnorm (q d) d
  have hsum : Summable (fun x : ℕ × ℕ => k x.1 * (x.1 : ℝ) ^ (-σ) * (q x.2 * (x.2 : ℝ) ^ (-σ))) :=
    summable_mul_of_summable_norm (f := fun j : ℕ => k j * (j : ℝ) ^ (-σ))
      (g := fun d : ℕ => q d * (d : ℝ) ^ (-σ)) hk' hq'
  have hfib := ((hk'.of_norm).hasSum.mul (hq'.of_norm).hasSum hsum).tsum_fiberwise
    (fun p : ℕ × ℕ => p.1 * p.2)
  refine hfib.congr_fun fun n => ?_
  have h0 : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (neg_ne_zero.mpr hσ.ne')
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
        k p.val.1 * (p.val.1 : ℝ) ^ (-σ) * (q p.val.2 * (p.val.2 : ℝ) ^ (-σ)) = 0 := by
      rintro ⟨⟨a, b⟩, hp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero] at hp
      rcases hp with rfl | rfl <;> simp [h0]
    simp [hzero, RHTower.dirichletConv]
  · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
      Finset.tsum_subtype' n.divisorsAntidiagonal
        fun p => k p.1 * (p.1 : ℝ) ^ (-σ) * (q p.2 * (p.2 : ℝ) ^ (-σ)),
      Nat.sum_divisorsAntidiagonal (fun a b => k a * (a : ℝ) ^ (-σ) * (q b * (b : ℝ) ^ (-σ))),
      RHTower.dirichletConv, sum_mul]
    refine sum_congr rfl fun j hj => ?_
    have hn' : (n : ℝ) = (j : ℝ) * ((n / j : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hj)]
    rw [hn', Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

/-- `|k ⋆ q| ≤ |k| ⋆ |q|` pointwise. -/
theorem abs_dirichletConv_le (k q : ℕ → ℝ) (n : ℕ) :
    |RHTower.dirichletConv k q n| ≤ RHTower.dirichletConv (fun j => |k j|) (fun d => |q d|) n := by
  unfold RHTower.dirichletConv
  exact (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun _ _ => abs_mul _ _))

/-- **The pole law for convolutions beyond the critical Wiener algebra.** Let `0 < ε < 1/2`, let
`q ≥ 0` lie in `𝒞(K, ε)` with `Σ q(d) d^{-(1−ε)} = ∞`, and let `Σ_j |k(j)| j^{-(1−ε)} < ∞` with
`Σ_j k(j) j^{-(1−ε)} ≠ 0`. Then the receiver of `k ⋆ q` is unbounded: its Dirichlet series is
`K(σ) Q(σ)` with `K(σ) → K(1 − ε) ≠ 0` and `Q(σ) → ∞` as `σ ↓ 1 − ε`. -/
theorem not_receiverBounded_dirichletConv_of_not_summable {K ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {q : ℕ → ℝ} (hq : ∀ d, 0 ≤ q d) (hclass : DampedClass K ε q)
    (hdiv : ¬ Summable (fun d : ℕ => q d * (d : ℝ) ^ (-(1 - ε))))
    {k : ℕ → ℝ} (hk : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 - ε))))
    (hK : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) ≠ 0) :
    ¬ ReceiverBounded (RHTower.dirichletConv k q) := by
  have ha : 1 / 2 < 1 - ε := by linarith
  have ha1 : 1 - ε < 1 := by linarith
  have ha0 : 0 < 1 - ε := by linarith
  -- absolute convergence above the abscissa
  have hkθ : ∀ θ, 1 - ε ≤ θ → Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-θ)) := fun θ hθ =>
    hk.of_nonneg_of_le (fun j => by positivity) fun j =>
      mul_le_mul_of_nonneg_left (rpow_neg_le_of_le ha0 hθ j) (abs_nonneg _)
  have hqθ : ∀ θ, 1 - ε < θ → Summable (fun d : ℕ => |q d| * (d : ℝ) ^ (-θ)) := fun _ hθ =>
    summable_abs_mul_rpow_of_dampedClass hε hclass hθ
  have habs : ∀ θ, 1 - ε < θ →
      Summable (fun n : ℕ => |RHTower.dirichletConv k q n| * (n : ℝ) ^ (-θ)) := fun θ hθ => by
    have h := (hasSum_dirichletConv_mul_rpow (k := fun j => |k j|) (q := fun d => |q d|)
      (by linarith) (by simpa only [abs_abs] using hkθ θ hθ.le)
      (by simpa only [abs_abs] using hqθ θ hθ)).summable
    exact h.of_nonneg_of_le (fun n => by positivity) fun n =>
      mul_le_mul_of_nonneg_right (abs_dirichletConv_le k q n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine not_receiverBounded_of_tendsto_abs_dirichletSeries ha ha1 habs ?_
  -- `|K(σ)| → |K(1 − ε)| > 0` and `|Q(σ)| → ∞`
  have hKt := (tendsto_dirichletSeries_nhdsGT ha0 hk).abs
  have hQt := tendsto_abs_atTop_atTop.comp (tendsto_dirichletSeries_atTop_of_not_summable ha0 hq
    (fun σ hσ => (hqθ σ hσ).congr fun d => by rw [abs_of_nonneg (hq d)]) hdiv)
  refine (Filter.Tendsto.pos_mul_atTop (abs_pos.mpr hK) hKt hQt).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [(hasSum_dirichletConv_mul_rpow (by linarith [Set.mem_Ioi.mp hσ]) (hkθ σ (le_of_lt hσ))
    (hqθ σ hσ)).tsum_eq, abs_mul]
  rfl

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
