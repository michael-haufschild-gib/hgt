import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor

/-!
# Regular spectral tails give Jordan-totient rescaled limits

The completed conductor energies `E_m(c)` of a profile `φ` tend to `0` as the overlap grows: the
fixed-overlap limit of the complete Weil family degenerates. This file computes what survives after
rescaling, when the spectral tail `T(x) = ∫_x^∞ |φ̂(2πt)|² dt` of the profile is regular,
`x^β T(x) → A`.

* **Conductor one** (`tendsto_rpow_mul_completedShellEnergy`): `c^β E(c) → (2A/M) Z(β+1)` with
  `Z(k) = Σ_{n≥1} n^{-k}`. The repayment series `E(c) = (2/M) Σ_n n⁻¹ T(nc)` is rescaled termwise and
  Tannery's theorem passes to the limit.
* **Every conductor, Möbius form** (`tendsto_rpow_mul_completedConductorEnergy`):
  `c^β E_m(c) → (2A/M) Z(β+1) J_{β+1}(m)/φ(m)`, `J_k(m) = Σ_{d∣m} μ(m/d) d^k` Jordan's totient.
  The conductor energy is the Möbius combination of the conductor-one energy at the star overlaps
  `c/d`, and the star at depth `d` carries the weight `d^β`.
* **Every conductor, coprime form** (`tendsto_rpow_mul_completedConductorEnergy_coprime`):
  the same limit is `(2A/(Mφ(m))) m^{β+1} Σ_{(n,m)=1} n^{-(β+1)}`, from the coprime repayment
  series. It is positive whenever `A > 0` (`jordanLimit_pos`).

So the rescaled limit of the degenerating family is a positive diagonal form whose coefficients are a
multiplicative arithmetic function of the conductor: the **Jordan-totient form**. The comparison of
the two forms of the limit is the identity `Z(k) J_k(m) = m^k Σ_{(n,m)=1} n^{-k}`
(`zetaSum_mul_jordanTotient_eq`), read off a degeneration.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The spectral tail `T(x) = ∫_x^∞ |φ̂(2πt)|² dt` of a profile. -/
def spectralTail (φ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Ioi x, shellSpectrum φ t

/-- Jordan's totient with real exponent, `J_k(m) = Σ_{d∣m} μ(m/d) d^k`. -/
def jordanTotient (k : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ k

/-- The zeta sum `Z(k) = Σ_{n≥1} n^{-k}`. -/
def zetaSum (k : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-k)

/-- The coprime zeta sum `Σ_{n≥1, (n,m)=1} n^{-k}`. -/
def coprimeZetaSum (k : ℝ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, if Nat.Coprime m (n + 1) then ((n : ℝ) + 1) ^ (-k) else 0

theorem summable_shift_rpow_neg {k : ℝ} (hk : 1 < k) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-k) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -k < -1))
  refine h.congr fun n => ?_
  push_cast
  rfl

theorem summable_coprime_shift_rpow_neg {k : ℝ} (hk : 1 < k) (m : ℕ) :
    Summable fun n : ℕ => if Nat.Coprime m (n + 1) then ((n : ℝ) + 1) ^ (-k) else 0 :=
  (summable_shift_rpow_neg hk).of_nonneg_of_le
    (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> [exact le_rfl; positivity])

variable {φ : ℝ → ℝ}

theorem shellSpectrum_nonneg (t : ℝ) : 0 ≤ shellSpectrum φ t := by
  unfold shellSpectrum
  positivity

theorem integrable_shellSpectrum (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) : Integrable (shellSpectrum φ) := by
  have h := (RHTower.integrable_normSq_paperFT_ofReal hφ (hasCompactSupport_profile hsupp)).comp_mul_left'
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [shellSpectrum]

theorem spectralTail_nonneg (x : ℝ) : 0 ≤ spectralTail φ x :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t

theorem spectralTail_le_integral (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) (x : ℝ) :
    spectralTail φ x ≤ ∫ t, shellSpectrum φ t :=
  setIntegral_le_integral (integrable_shellSpectrum hφ hsupp)
    (Eventually.of_forall fun t => shellSpectrum_nonneg t)

/-- A convergent rescaled tail is bounded on `[1, ∞)`. -/
theorem exists_rpow_mul_spectralTail_le (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) {β A : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 A)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ^ β * spectralTail φ x ≤ B := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hT.eventually (gt_mem_nhds (lt_add_one A)))
  set I := ∫ t, shellSpectrum φ t
  have hI : 0 ≤ I := integral_nonneg fun t => shellSpectrum_nonneg t
  refine ⟨max (A + 1) (max X 1 ^ β * I) ⊔ 0, le_sup_right, fun x hx => ?_⟩
  refine le_sup_of_le_left ?_
  rcases le_total X x with hXx | hxX
  · exact le_max_of_le_left (hX x hXx).le
  · refine le_max_of_le_right (mul_le_mul ?_ (spectralTail_le_integral hφ hsupp x)
      (spectralTail_nonneg x) (by positivity))
    exact Real.rpow_le_rpow (by linarith) (hxX.trans (le_max_left _ _)) hβ.le

section Limits

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- The rescaled repayment series of the conductor-one energy. -/
theorem hasSum_rpow_mul_completedShellEnergy {β : ℝ} {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => 2 / (∫ u, φ u ^ 2) * (((n : ℝ) + 1) ^ (-(β + 1)) *
        ((((n : ℝ) + 1) * c) ^ β * spectralTail φ (((n : ℝ) + 1) * c))))
      (c ^ β * completedShellEnergy φ c) := by
  refine ((hasSum_completedShellEnergy hφ hsupp hM hc).mul_left (c ^ β)).congr_fun fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.mul_rpow hn.le hc.le, Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
  unfold spectralTail
  field_simp

/-- **The conductor-one rescaled limit.** If `x^β T(x) → A`, then `c^β E(c) → (2A/M) Z(β+1)`. -/
theorem tendsto_rpow_mul_completedShellEnergy {β A : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 A)) :
    Tendsto (fun c => c ^ β * completedShellEnergy φ c) atTop
      (𝓝 (2 / (∫ u, φ u ^ 2) * A * zetaSum (β + 1))) := by
  obtain ⟨B, hB0, hB⟩ := exists_rpow_mul_spectralTail_le hφ hsupp hβ hT
  set M := ∫ u, φ u ^ 2
  have hsum := summable_shift_rpow_neg (k := β + 1) (by linarith)
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun c (n : ℕ) => 2 / M * (((n : ℝ) + 1) ^ (-(β + 1)) *
      ((((n : ℝ) + 1) * c) ^ β * spectralTail φ (((n : ℝ) + 1) * c))))
    (g := fun n => 2 / M * (((n : ℝ) + 1) ^ (-(β + 1)) * A))
    (bound := fun n => 2 / M * (((n : ℝ) + 1) ^ (-(β + 1)) * B))
    ((hsum.mul_right B).mul_left (2 / M))
    (fun n => by
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact ((hT.comp (tendsto_id.const_mul_atTop hn)).const_mul _).const_mul _)
    (by
      filter_upwards [eventually_ge_atTop 1] with c hc n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
      have hx : 1 ≤ ((n : ℝ) + 1) * c := one_le_mul_of_one_le_of_one_le hn hc
      have hpos : 0 ≤ ((((n : ℝ) + 1) * c) ^ β * spectralTail φ (((n : ℝ) + 1) * c)) :=
        mul_nonneg (by positivity) (spectralTail_nonneg _)
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      exact hB _ hx)
  have heq : ∀ᶠ c in atTop, (∑' n : ℕ, 2 / M * (((n : ℝ) + 1) ^ (-(β + 1)) *
      ((((n : ℝ) + 1) * c) ^ β * spectralTail φ (((n : ℝ) + 1) * c)))) =
        c ^ β * completedShellEnergy φ c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact (hasSum_rpow_mul_completedShellEnergy hφ hsupp hM hc).tsum_eq
  have hval : (∑' n : ℕ, 2 / M * (((n : ℝ) + 1) ^ (-(β + 1)) * A)) = 2 / M * A * zetaSum (β + 1) := by
    rw [zetaSum, tsum_mul_left, tsum_mul_right]
    ring
  rw [hval] at hlim
  exact hlim.congr' heq

/-- **The Jordan-totient rescaled limit.** If `x^β T(x) → A`, then for every conductor `m ≥ 1`,
`c^β E_m(c) → (2A/M) Z(β+1) J_{β+1}(m)/φ(m)`. -/
theorem tendsto_rpow_mul_completedConductorEnergy {β A : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 A)) (m : ℕ) :
    Tendsto (fun c => c ^ β * completedConductorEnergy φ c m) atTop
      (𝓝 (2 / (∫ u, φ u ^ 2) * A * zetaSum (β + 1) * jordanTotient (β + 1) m / m.totient)) := by
  set L := 2 / (∫ u, φ u ^ 2) * A * zetaSum (β + 1)
  have h1 := tendsto_rpow_mul_completedShellEnergy hφ hsupp hM hβ hT
  have hd : ∀ d ∈ m.divisors, Tendsto
      (fun c => (ArithmeticFunction.moebius (m / d) : ℝ) * d * (c ^ β * completedShellEnergy φ (c / d)))
      atTop (𝓝 ((ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ (β + 1) * L)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hcomp := (h1.comp (tendsto_id.atTop_div_const hd0)).const_mul ((d : ℝ) ^ β)
    have hc : Tendsto (fun c => c ^ β * completedShellEnergy φ (c / d)) atTop
        (𝓝 ((d : ℝ) ^ β * L)) := by
      refine hcomp.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with c hc
      simp only [Function.comp, id]
      rw [Real.div_rpow hc.le hd0.le]
      field_simp
    convert hc.const_mul ((ArithmeticFunction.moebius (m / d) : ℝ) * d) using 2
    rw [Real.rpow_add hd0, Real.rpow_one]
    ring
  have hsum := (tendsto_finsetSum m.divisors hd).div_const (m.totient : ℝ)
  have hval : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ (β + 1) * L) /
      m.totient = L * jordanTotient (β + 1) m / m.totient := by
    rw [jordanTotient, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hval] at hsum
  refine hsum.congr' (Eventually.of_forall fun c => ?_)
  simp only [completedConductorEnergy]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun d _ => by ring

/-- The rescaled coprime repayment series of a conductor energy. -/
theorem hasSum_rpow_mul_completedConductorEnergy {β c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    HasSum (fun n : ℕ => if Nat.Coprime m (n + 1) then
        2 / ((∫ u, φ u ^ 2) * m.totient) * (m : ℝ) ^ (β + 1) * (((n : ℝ) + 1) ^ (-(β + 1)) *
          ((((n : ℝ) + 1) * c / m) ^ β * spectralTail φ (((n : ℝ) + 1) * c / m))) else 0)
      (c ^ β * completedConductorEnergy φ c m) := by
  refine ((hasSum_completedConductorEnergy hφ hsupp hM hc hm).mul_left (c ^ β)).congr_fun
    fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  split_ifs
  · rw [Real.div_rpow (by positivity) hm0.le, Real.mul_rpow hn.le hc.le, Real.rpow_neg hn.le,
      Real.rpow_add hn, Real.rpow_add hm0, Real.rpow_one, Real.rpow_one]
    unfold spectralTail
    have : (0 : ℝ) < (n : ℝ) + 1 := hn
    have hmβ : (0 : ℝ) < (m : ℝ) ^ β := Real.rpow_pos_of_pos hm0 β
    have hnβ : (0 : ℝ) < ((n : ℝ) + 1) ^ β := Real.rpow_pos_of_pos hn β
    field_simp
  · simp

/-- **The coprime form of the rescaled limit.** If `x^β T(x) → A`, then
`c^β E_m(c) → (2A/(Mφ(m))) m^{β+1} Σ_{(n,m)=1} n^{-(β+1)}`. -/
theorem tendsto_rpow_mul_completedConductorEnergy_coprime {β A : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 A)) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun c => c ^ β * completedConductorEnergy φ c m) atTop
      (𝓝 (2 / ((∫ u, φ u ^ 2) * m.totient) * (m : ℝ) ^ (β + 1) * A *
        coprimeZetaSum (β + 1) m)) := by
  obtain ⟨B, hB0, hB⟩ := exists_rpow_mul_spectralTail_le hφ hsupp hβ hT
  set K := 2 / ((∫ u, φ u ^ 2) * m.totient) * (m : ℝ) ^ (β + 1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hK : 0 ≤ K := by
    have := Nat.totient_pos.mpr hm
    positivity
  have hsum := summable_coprime_shift_rpow_neg (k := β + 1) (by linarith) m
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun c (n : ℕ) => if Nat.Coprime m (n + 1) then K * (((n : ℝ) + 1) ^ (-(β + 1)) *
      ((((n : ℝ) + 1) * c / m) ^ β * spectralTail φ (((n : ℝ) + 1) * c / m))) else 0)
    (g := fun n => if Nat.Coprime m (n + 1) then K * (((n : ℝ) + 1) ^ (-(β + 1)) * A) else 0)
    (bound := fun n => K * B * (if Nat.Coprime m (n + 1) then ((n : ℝ) + 1) ^ (-(β + 1)) else 0))
    (hsum.mul_left (K * B))
    (fun n => by
      split_ifs
      · have hn : (0 : ℝ) < ((n : ℝ) + 1) / m := by positivity
        have hlin : Tendsto (fun c : ℝ => ((n : ℝ) + 1) * c / m) atTop atTop :=
          (tendsto_id.const_mul_atTop hn).congr fun c => by simp only [id]; ring
        exact ((hT.comp hlin).const_mul _).const_mul _
      · exact tendsto_const_nhds)
    (by
      filter_upwards [eventually_ge_atTop (m : ℝ)] with c hc n
      split_ifs
      · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
        have hx : 1 ≤ ((n : ℝ) + 1) * c / m := by
          rw [le_div_iff₀ hm0, one_mul]
          nlinarith
        have hpos : 0 ≤ ((((n : ℝ) + 1) * c / m) ^ β * spectralTail φ (((n : ℝ) + 1) * c / m)) :=
          mul_nonneg (by positivity) (spectralTail_nonneg _)
        rw [Real.norm_of_nonneg (by positivity)]
        calc K * (((n : ℝ) + 1) ^ (-(β + 1)) *
              ((((n : ℝ) + 1) * c / m) ^ β * spectralTail φ (((n : ℝ) + 1) * c / m)))
            ≤ K * (((n : ℝ) + 1) ^ (-(β + 1)) * B) := by gcongr; exact hB _ hx
          _ = K * B * ((n : ℝ) + 1) ^ (-(β + 1)) := by ring
      · simp)
  have heq : ∀ᶠ c in atTop, (∑' n : ℕ, if Nat.Coprime m (n + 1) then K * (((n : ℝ) + 1) ^ (-(β + 1)) *
      ((((n : ℝ) + 1) * c / m) ^ β * spectralTail φ (((n : ℝ) + 1) * c / m))) else 0) =
        c ^ β * completedConductorEnergy φ c m := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact (hasSum_rpow_mul_completedConductorEnergy hφ hsupp hM hc hm).tsum_eq
  have hval : (∑' n : ℕ, if Nat.Coprime m (n + 1) then K * (((n : ℝ) + 1) ^ (-(β + 1)) * A) else 0) =
      K * A * coprimeZetaSum (β + 1) m := by
    rw [coprimeZetaSum, ← tsum_mul_left]
    congr 1
    funext n
    split_ifs <;> ring
  rw [hval] at hlim
  exact hlim.congr' heq

end Limits

/-- The coprime zeta sum is at least its first term. -/
theorem one_le_coprimeZetaSum {k : ℝ} (hk : 1 < k) (m : ℕ) : 1 ≤ coprimeZetaSum k m := by
  have hs := summable_coprime_shift_rpow_neg hk m
  have h0 := hs.le_tsum 0 (fun n _ => by split_ifs <;> positivity)
  unfold coprimeZetaSum
  simpa [Nat.coprime_one_right] using h0

/-- **Positivity of the rescaled limit.** With a positive tail constant the limit of `c^β E_m(c)` is
positive for every conductor. -/
theorem jordanLimit_pos {β A M : ℝ} (hβ : 0 < β) (hA : 0 < A) (hM : 0 < M) {m : ℕ} (hm : 0 < m) :
    0 < 2 / (M * m.totient) * (m : ℝ) ^ (β + 1) * A * coprimeZetaSum (β + 1) m := by
  have := Nat.totient_pos.mpr hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have := one_le_coprimeZetaSum (k := β + 1) (by linarith) m
  have : (0 : ℝ) < (m : ℝ) ^ (β + 1) := Real.rpow_pos_of_pos hm0 _
  positivity

/-- **Two readings of one limit.** If some profile has a positive regular tail of exponent `β`, the
Möbius and coprime forms of its rescaled limit agree: `Z(β+1) J_{β+1}(m) = m^{β+1} Σ_{(n,m)=1} n^{-(β+1)}`. -/
theorem zetaSum_mul_jordanTotient_eq (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {β A : ℝ} (hβ : 0 < β)
    (hA : A ≠ 0) (hT : Tendsto (fun x => x ^ β * spectralTail φ x) atTop (𝓝 A)) {m : ℕ}
    (hm : 0 < m) :
    zetaSum (β + 1) * jordanTotient (β + 1) m = (m : ℝ) ^ (β + 1) * coprimeZetaSum (β + 1) m := by
  have h := tendsto_nhds_unique (tendsto_rpow_mul_completedConductorEnergy hφ hsupp hM hβ hT m)
    (tendsto_rpow_mul_completedConductorEnergy_coprime hφ hsupp hM hβ hT hm)
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hM' := hM.ne'
  have h2 : (2 * A / ((∫ u, φ u ^ 2) * m.totient)) * (zetaSum (β + 1) * jordanTotient (β + 1) m) =
      (2 * A / ((∫ u, φ u ^ 2) * m.totient)) * ((m : ℝ) ^ (β + 1) * coprimeZetaSum (β + 1) m) := by
    rw [div_eq_mul_inv] at h
    linear_combination h
  exact mul_left_cancel₀ (div_ne_zero (mul_ne_zero two_ne_zero hA) (by positivity)) h2

end GaloisForLFunctions.ArithmeticDegenerationTheory
