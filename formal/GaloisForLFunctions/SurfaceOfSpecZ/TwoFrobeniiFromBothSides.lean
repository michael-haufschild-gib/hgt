import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSuffice
import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# Two Frobenii from both sides

`TwoFrobeniiSuffice` samples the one-sided planes `⟨Γ_1, Γ_{pᵃqᵇ}⟩` and needs an attained top: their
lags `a log p + b log q`, `a, b ≥ 0`, are discrete. The planes `⟨Γ_m, Γ_n⟩` with `m, n` in the monoid
`⟨p, q⟩` have the lags `log m − log n`, which fill the group `ℤ log p + ℤ log q`, dense in `ℝ`
because `pᴹ ≠ qᴺ` (`RHTower.dense_addSubgroup_log_primes`). Hasse–Weil on these planes is two-sided,
so continuity of the spline orbit extends it to every lag, and no attainment is needed:

**Theorem** (`riemannHypothesis_iff_twoPrimePlanes_hasseWeil`). For two distinct primes `p, q`, RH
holds iff `|c_B(log m − log n)| ≤ c_B(0)` for all `m, n` of the form `pᵃqᵇ`: Hasse–Weil on the planes
of the Frobenius graphs of the rank-two monoid of degrees.

This is `HasseWeilForPairsOfPrimeDegrees` with two primes in place of all of them, Kronecker's
density in place of the prime number theorem. As a count door
(`riemannHypothesis_iff_twoPrimePlaneCounts`): RH iff every plane `⟨Γ_m, Γ_n⟩`, `m, n ∈ ⟨p, q⟩`,
carries an `ℕ`-count on `ℤ²` with Tate limit its defect `c_B(0)x² + 2c_B(log m − log n)xy + c_B(0)y²`.
By Hecke invariance the defect depends only on `m/n ∈ p^ℤ q^ℤ`: one binary count per point of the
lattice `ℤ²`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography

variable {p q : ℕ}

theorem log_pow_mul_pow (hp : p.Prime) (hq : q.Prime) (a b : ℕ) :
    Real.log ((p ^ a * q ^ b : ℕ) : ℝ) = a * Real.log p + b * Real.log q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  push_cast
  rw [Real.log_mul (pow_pos hp0 _).ne' (pow_pos hq0 _).ne', Real.log_pow, Real.log_pow]

/-- Every element of `ℤ log p + ℤ log q` is a lag `log m − log n` of the monoid `⟨p, q⟩`. -/
theorem exists_lag_of_mem_closure (hp : p.Prime) (hq : q.Prime) {t : ℝ}
    (ht : t ∈ AddSubgroup.closure {Real.log p, Real.log q}) :
    ∃ a b a' b' : ℕ, t = Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ) := by
  have hint : ∃ m n : ℤ, t = m * Real.log p + n * Real.log q := by
    induction ht using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨1, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨0, 1, by simp [hx]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, n, rfl⟩ := hx
      obtain ⟨m', n', rfl⟩ := hy
      exact ⟨m + m', n + n', by push_cast; ring⟩
    | neg x _ hx =>
      obtain ⟨m, n, rfl⟩ := hx
      exact ⟨-m, -n, by push_cast; ring⟩
  obtain ⟨m, n, rfl⟩ := hint
  refine ⟨m.toNat, n.toNat, (-m).toNat, (-n).toNat, ?_⟩
  rw [log_pow_mul_pow hp hq, log_pow_mul_pow hp hq]
  have hm : ((m.toNat : ℤ) : ℝ) - (((-m).toNat : ℤ) : ℝ) = m := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  have hn : ((n.toNat : ℤ) : ℝ) - (((-n).toNat : ℤ) : ℝ) = n := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  push_cast at hm hn
  rw [← hm, ← hn]
  ring

/-- **Hasse–Weil on the planes of two Frobenii is RH.** -/
theorem riemannHypothesis_iff_twoPrimePlanes_hasseWeil (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ a b a' b' : ℕ, zetaScalingDatum.HasseWeilAt splineCycle
      (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ)) := by
  rw [riemannHypothesis_iff_splineOrbit_hasseWeil]
  constructor
  · intro h a b a' b'; exact h _
  · intro h
    have hcont := continuous_zetaOrbitCorr' splineCycle
    have hclosed : IsClosed {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      simp only [ScalingDatum.HasseWeilAt]
      exact isClosed_le (continuous_abs.comp hcont) continuous_const
    have hsub : ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ) ⊆
        {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      intro t ht
      obtain ⟨a, b, a', b', rfl⟩ := exists_lag_of_mem_closure hp hq ht
      exact h a b a' b'
    have huniv := ((RHTower.dense_addSubgroup_log_primes hp hq hpq).mono hsub).closure_eq
    rw [hclosed.closure_eq] at huniv
    intro t
    have : t ∈ {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by rw [huniv]; trivial
    exact this

/-- The defect of the plane `⟨Γ_m, Γ_n⟩` at the lag `t = log m − log n`. -/
def lagDefect (t : ℝ) (v : ℤ × ℤ) : ℝ :=
  zetaScalingDatum.orbitCorr splineCycle 0 * (v.1 : ℝ) ^ 2 +
    2 * zetaScalingDatum.orbitCorr splineCycle t * v.1 * v.2 +
      zetaScalingDatum.orbitCorr splineCycle 0 * (v.2 : ℝ) ^ 2

theorem lagDefect_smul (t : ℝ) (m : ℕ) (v : ℤ × ℤ) :
    lagDefect t (m • v) = (m : ℝ) ^ 2 * lagDefect t v := by
  obtain ⟨a, b⟩ := v
  simp only [lagDefect, Prod.smul_mk, nsmul_eq_mul]
  push_cast
  ring

/-- A plane carries a count with Tate limit its defect iff Hasse–Weil holds at its lag. -/
theorem exists_lagCount_iff (t : ℝ) :
    (∃ K : ℤ × ℤ → ℕ, ∀ v : ℤ × ℤ,
      Tendsto (fun m : ℕ => (K (m • v) : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (lagDefect t v))) ↔
      zetaScalingDatum.HasseWeilAt splineCycle t := by
  constructor
  · rintro ⟨K, hK⟩
    have hnn : ∀ v : ℤ × ℤ, 0 ≤ lagDefect t v := fun v =>
      nonneg_of_tateLimit (M := ℤ × ℤ) (K := fun w => (K w : ℝ)) (fun _ => Nat.cast_nonneg _)
        (hK v)
    rw [← frobeniusPair_defect_nonneg_iff]
    intro u w
    have h1 := hnn (1, 1)
    have h2 := hnn (1, -1)
    simp only [lagDefect] at h1 h2
    push_cast at h1 h2
    set c0 := zetaScalingDatum.orbitCorr splineCycle 0
    set c := zetaScalingDatum.orbitCorr splineCycle t
    have hc0 : 0 ≤ c0 := by linarith
    nlinarith [sq_nonneg (u + w), sq_nonneg (u - w),
      mul_nonneg (by linarith : 0 ≤ c0 - c) (sq_nonneg (u - w)),
      mul_nonneg (by linarith : 0 ≤ c0 + c) (sq_nonneg (u + w))]
  · intro h
    have hpsd := (frobeniusPair_defect_nonneg_iff splineCycle t).mpr h
    refine ⟨fun v => ⌊lagDefect t v⌋₊, fun v => ?_⟩
    have hv : 0 ≤ lagDefect t v := by
      have := hpsd v.1 v.2
      unfold lagDefect; linarith
    refine (tendsto_floor_div_sq hv).congr' ?_
    filter_upwards with m
    rw [lagDefect_smul]

/-- **The count door at the planes of two Frobenii.** -/
theorem riemannHypothesis_iff_twoPrimePlaneCounts (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ a b a' b' : ℕ, ∃ K : ℤ × ℤ → ℕ, ∀ v : ℤ × ℤ,
      Tendsto (fun m : ℕ => (K (m • v) : ℝ) / (m : ℝ) ^ 2) atTop
        (𝓝 (lagDefect (Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ))
          v)) := by
  rw [riemannHypothesis_iff_twoPrimePlanes_hasseWeil hp hq hpq]
  exact forall_congr' fun a => forall_congr' fun b => forall_congr' fun a' => forall_congr' fun b' =>
    (exists_lagCount_iff _).symm

end GaloisForLFunctions.SurfaceOfSpecZ
