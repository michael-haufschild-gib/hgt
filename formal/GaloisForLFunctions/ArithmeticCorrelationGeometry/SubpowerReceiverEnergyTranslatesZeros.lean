import GaloisForLFunctions.ArithmeticCorrelationGeometry.ChargedBoundariesAreCriticalAtAQuarter
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# Subpower receiver energy translates zeros

The damped Möbius receiver `A_ε(n) = Σ_{d ≤ n} μ(d) d^{−ε} ⌊n/d⌋ − n/ζ(1+ε)` has Mellin pairing
`Φ(s) = Σ_n A_ε(n)(n^{−s} − (n+1)^{−s}) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))`. Bounded energy
(admission) makes `Φ` holomorphic on `Re s > ½`
(`TransHorizonIncidenceMechanics.differentiableOn_complexMellinPairing`). Here the energy is only
assumed to grow polynomially.

* **Weighted summability** (`summable_mul_rpow_neg_of_partialSum_le`,
  `summable_abs_mul_rpow_of_energy_growth`). If `E(T) = Σ_{n ≤ T} A(n)²/(n(n+1)) ≤ C (T+1)^κ`, then
  `Σ |A(n)| n^{−b−1} < ∞` for every `b > (1+κ)/2` (Abel summation against `n^{−γ}`, `κ < γ < 2b − 1`,
  and the arithmetic–geometric inequality).
* **Holomorphy** (`differentiableOn_complexMellinPairing_of_energy_growth`): `Φ` is holomorphic on
  `Re s > (1+κ)/2`.
* **Translation** (`riemannZeta_sub_eq_zero_of_energy_growth`). The cleared function
  `H(s) = R(s+ε)(Φ(s) + ζ(s)/ζ(1+ε)) − (s+ε−1)ζ(s)`, `R(w) = (w−1)ζ(w)`, is holomorphic on the strip
  `(1+κ)/2 < Re s < 1` and vanishes on `(1−ε, 1)`, hence identically. At `s = ρ − ε` for a zero `ρ`
  with `Re ρ > (1+κ)/2 + ε` this reads `ζ(ρ − ε) = 0`.
* **Subpower energy at every damping is RH** (`riemannHypothesis_of_subpower_energy`). If for
  every `0 < ε < ½` the energy is `O(T^κ)` for every `κ > 0`, an off-line zero `ρ` would translate to
  zeros `ρ − ε` for a whole interval of `ε`, which accumulate.
-/

open Complex Filter Topology Finset Set
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open TransHorizonIncidenceMechanics BezoutValuationIncidence ArithmeticContinuationAndCriticalEnergy

/-! ### Weighted summability -/

/-- **Abel summation for nonnegative sequences.** Partial sums `≤ C (T+1)^κ` make `Σ e_n n^{−γ}`
converge for `γ > κ`. -/
theorem summable_mul_rpow_neg_of_partialSum_le {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n) (he0 : e 0 = 0)
    {C κ γ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hκγ : κ < γ)
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, e n ≤ C * ((T : ℝ) + 1) ^ κ) :
    Summable fun n : ℕ => e n * (n : ℝ) ^ (-γ) := by
  have hS : ∀ n : ℕ, ‖∑ i ∈ range (n + 1), ((e i : ℝ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ κ := by
    intro n
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun i _ => he i), range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), he0, zero_add]
    have hIcc : Finset.Ico (0 + 1) (n + 1) = Finset.Icc 1 n := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIcc]
    exact hE n
  have hbound := fun N : ℕ => norm_sum_Ioc_mul_rpow_neg_le (c := fun i => ((e i : ℝ) : ℂ)) hC hκ hκγ
    hS 0 N
  refine summable_of_sum_range_le (fun n => mul_nonneg (he n) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (c := C * (2 + γ * 2 ^ (γ + 1) / (γ - κ)) * (((0 : ℕ) : ℝ) + 1) ^ (κ - γ)) fun N => ?_
  have hN := hbound N
  have hreal : ∑ j ∈ Ioc 0 N, ((e j : ℝ) : ℂ) * ((((j : ℝ) ^ (-γ)) : ℝ) : ℂ) =
      ((∑ j ∈ Ioc 0 N, e j * (j : ℝ) ^ (-γ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hN
  calc ∑ i ∈ range N, e i * (i : ℝ) ^ (-γ) ≤ ∑ i ∈ range (N + 1), e i * (i : ℝ) ^ (-γ) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ N))
          fun i _ _ => mul_nonneg (he i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ∑ j ∈ Ioc 0 N, e j * (j : ℝ) ^ (-γ) := by
        rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), he0, zero_mul, zero_add]
        congr 1
    _ ≤ _ := (le_abs_self _).trans hN


/-- **Weighted summability.** Energy `O((T+1)^κ)` makes `Σ |f(n)| n^{−b−1}` converge for every
`b > (1+κ)/2`. -/
theorem summable_abs_mul_rpow_of_energy_growth {f : ℕ → ℝ} (hf0 : f 0 = 0) {C κ b : ℝ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hb : (1 + κ) / 2 < b)
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ C * ((T : ℝ) + 1) ^ κ) :
    Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-b - 1) := by
  set γ := (κ + (2 * b - 1)) / 2 with hγ
  have hκγ : κ < γ := by rw [hγ]; linarith
  have hγb : γ - 2 * b < -1 := by rw [hγ]; linarith
  have h1 := summable_mul_rpow_neg_of_partialSum_le
    (e := fun n => f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) (fun n => by positivity) (by simp [hf0])
    hC hκ hκγ hE
  have h2 : Summable fun n : ℕ => 2 * (n : ℝ) ^ (γ - 2 * b) :=
    (Real.summable_nat_rpow.mpr hγb).mul_left 2
  refine (h1.add h2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf0]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set r := Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) with hr
  set w := (n : ℝ) ^ (γ / 2) with hw
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hw0 : 0 < w := Real.rpow_pos_of_pos hn0 _
  have hr2 : r ^ 2 = (n : ℝ) * ((n : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = (n : ℝ) ^ γ := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  set u := (n : ℝ) ^ (-b - 1) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hn0 _
  -- `|f| u = (|f|/(r w)) · (r w u)` and the arithmetic–geometric inequality
  have hsplit : |f n| * u = (|f n| / (r * w)) * (r * w * u) := by field_simp
  have hA : (|f n| / (r * w)) ^ 2 = f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-γ) := by
    rw [div_pow, mul_pow, hr2, hw2, sq_abs, Real.rpow_neg hn0.le]
    field_simp
  have hB : (r * w * u) ^ 2 ≤ 2 * (n : ℝ) ^ (γ - 2 * b) := by
    rw [mul_pow, mul_pow, hr2, hw2, hu, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    have hsum : (n : ℝ) ^ γ * (n : ℝ) ^ ((-b - 1) * ((2 : ℕ) : ℝ)) =
        (n : ℝ) ^ (γ - 2 * b) * (n : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num; ring_nf
    have hn2 : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hn0.le]; norm_num
    rw [mul_assoc, hsum, hn2]
    have hpos : 0 < (n : ℝ) ^ (γ - 2 * b) := Real.rpow_pos_of_pos hn0 _
    rw [show (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) ^ (γ - 2 * b) * ((n : ℝ) ^ 2)⁻¹) =
      (n : ℝ) ^ (γ - 2 * b) * (((n : ℝ) + 1) / n) by field_simp]
    have : ((n : ℝ) + 1) / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
    nlinarith
  have hamgm := two_mul_le_add_sq (|f n| / (r * w)) (r * w * u)
  rw [hA] at hamgm
  have hnn : 0 ≤ |f n| / (r * w) * (r * w * u) := by positivity
  nlinarith [hsplit]

/-- **Holomorphy beyond the energy exponent.** Energy `O((T+1)^κ)` makes the Mellin pairing
holomorphic on `Re s > (1+κ)/2`. -/
theorem differentiableOn_complexMellinPairing_of_energy_growth {f : ℕ → ℝ} (hf0 : f 0 = 0)
    {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hE : ∀ T : ℕ, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ C * ((T : ℝ) + 1) ^ κ) :
    DifferentiableOn ℂ (complexMellinPairing f) {s : ℂ | (1 + κ) / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : (1 + κ) / 2 < s₀.re := hs₀
  obtain ⟨b, hb, hbs⟩ : ∃ b : ℝ, (1 + κ) / 2 < b ∧ b < s₀.re :=
    ⟨((1 + κ) / 2 + s₀.re) / 2, by linarith, by linarith⟩
  obtain ⟨R, hR, hsR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ‖s₀‖ < R := ⟨‖s₀‖ + 1, by positivity, by linarith⟩
  set U : Set ℂ := {s | b < s.re} ∩ {s | ‖s‖ < R} with hU_def
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hs₀U : s₀ ∈ U := ⟨hbs, hsR⟩
  have hb0 : 0 < b := by linarith
  have hsum := (summable_abs_mul_rpow_of_energy_growth hf0 hC hκ hb hE).mul_left R
  have hdiff : DifferentiableOn ℂ (fun s => ∑' n : ℕ, (f n : ℂ) * complexMellinCell s n) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n s => (f n : ℂ) * complexMellinCell s n) hsum (fun n s hs => ?_) hU
      (fun n s hs => ?_)
    · have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by
        have h1 : b < s.re := hs.1
        rw [h, Complex.zero_re] at h1; linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      show DifferentiableAt ℂ (fun s => (f n : ℂ) * (((n : ℝ) : ℂ) ^ (-s) -
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))) s
      exact (differentiableAt_const _).mul
        ((differentiableAt_id.neg.const_cpow (Or.inr hs0)).sub
          (differentiableAt_id.neg.const_cpow (Or.inr hs0)))
    · show ‖(f n : ℂ) * complexMellinCell s n‖ ≤ R * (|f n| * (n : ℝ) ^ (-b - 1))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hf0]
      have hre : b < s.re := hs.1
      have hnorm : ‖s‖ < R := hs.2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |f n| * ‖complexMellinCell s n‖ ≤ |f n| * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
            mul_le_mul_of_nonneg_left (norm_complexMellinCell_le (by linarith) hn) (abs_nonneg _)
        _ ≤ |f n| * (R * (n : ℝ) ^ (-b - 1)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul hnorm.le ?_ (by positivity) hR)
              (abs_nonneg _)
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
        _ = R * (|f n| * (n : ℝ) ^ (-b - 1)) := by ring
  exact (hdiff.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

/-! ### Translation of zeros -/

theorem zetaResidueUnit_of_ne' {s : ℂ} (hs : s ≠ 1) :
    RHTower.zetaResidueUnit s = (s - 1) * riemannZeta s := by
  simp [RHTower.zetaResidueUnit, Function.update_of_ne hs]

/-- The damped Möbius weight is summable against `d^{−θ}` for `θ > 1 − ε`. -/
theorem summable_abs_pmPowerDampedRealWeight_mul {ε θ : ℝ} (hθ : 1 - ε < θ) :
    Summable fun d : ℕ => |pmPowerDampedRealWeight ε d| * (d : ℝ) ^ (-θ) := by
  have hs : Summable fun d : ℕ => (d : ℝ) ^ (-(ε + θ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine hs.of_nonneg_of_le (fun d => by positivity) fun d => ?_
  rw [pmPowerDampedRealWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [moebiusReal]; exact Real.rpow_nonneg le_rfl _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mul_assoc, ← Real.rpow_add hd0, show -ε + -θ = -(ε + θ) by ring]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hd0.le _) (abs_moebiusReal_le_one' d)

/-- The damped weight's Dirichlet series is `1/ζ(σ+ε)` for `σ + ε > 1`. -/
theorem ofReal_tsum_pmPowerDampedRealWeight {ε σ : ℝ} (h : 1 < σ + ε) :
    ((∑' d : ℕ, pmPowerDampedRealWeight ε d * (d : ℝ) ^ (-σ) : ℝ) : ℂ) =
      1 / riemannZeta ((σ + ε : ℝ) : ℂ) := by
  rw [← HTGeometry.ofReal_tsum_moebius_eq h]
  congr 2
  funext d
  rw [pmPowerDampedRealWeight, moebiusReal]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mul_assoc, ← Real.rpow_add hd0, show -ε + -σ = -(σ + ε) by ring]

/-- **Polynomial energy translates zeros.** If the receiver energy at damping `0 < ε < ½` is
`O((T+1)^κ)`, every zero `ρ` of `ζ` with `(1+κ)/2 + ε < Re ρ < 1` has `ζ(ρ − ε) = 0`. -/
theorem riemannZeta_sub_eq_zero_of_energy_growth {ε : ℝ} (hε : 0 < ε) {C κ : ℝ} (hC : 0 ≤ C)
    (hκ : 0 ≤ κ) (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : (1 + κ) / 2 + ε < ρ.re) (hre1 : ρ.re < 1) :
    riemannZeta (ρ - ε) = 0 := by
  set c := pmPowerDampedRealWeight ε
  set m := ∑' d : ℕ, c d / d with hm_def
  have hm : m = dampedDensity ε := (dampedDensity_eq_tsum hε).symm
  set A := weightCenteredPrefix c m
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero _ _
  have hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ := by
    intro T
    have h := weightPronicEnergy_pmPowerDamped ε T
    unfold weightPronicEnergy at h
    simp only [A, hm]
    rw [h]
    exact hE T
  have hΦ := differentiableOn_complexMellinPairing_of_energy_growth hA0 hC hκ hEA
  -- the strip and the cleared function
  set U : Set ℂ := {s : ℂ | (1 + κ) / 2 < s.re ∧ s.re < 1} with hU_def
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt ((1 + κ) / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected
  set H : ℂ → ℂ := fun s => RHTower.zetaResidueUnit (s + ε) *
    (complexMellinPairing A s + (m : ℂ) * riemannZeta s) - (s + ε - 1) * riemannZeta s with hH
  have hζU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta fun h1 => by
      have := hs.2; rw [h1, Complex.one_re] at this; exact lt_irrefl _ this).differentiableWithinAt
  have hRU : DifferentiableOn ℂ (fun s : ℂ => RHTower.zetaResidueUnit (s + ε)) U := fun s _ =>
    ((RHTower.analyticAt_zetaResidueUnit (s + ε)).differentiableAt.comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hHd : DifferentiableOn ℂ H U :=
    (hRU.mul ((hΦ.mono fun s hs => hs.1).add (hζU.const_mul _))).sub
      (((differentiableOn_id.add_const _).sub_const _).mul hζU)
  have hHa : AnalyticOnNhd ℂ H U := hHd.analyticOnNhd hUo
  -- `H` vanishes on `(1 − ε, 1)`
  have hκε : (1 + κ) / 2 < 1 - ε := by linarith
  have hzero : ∀ σ : ℝ, 1 - ε < σ → σ < 1 → H σ = 0 := by
    intro σ hσ hσ1
    have hσε : 1 < σ + ε := by linarith
    have hΦσ := complexMellinPairing_eq_zeta_mul (c := c) (θ := (1 - ε + σ) / 2)
      (by linarith) (by linarith) hσ1 (summable_abs_pmPowerDampedRealWeight_mul (by linarith))
    have hC := ofReal_tsum_pmPowerDampedRealWeight (ε := ε) hσε
    have hne1 : ((σ : ℂ) + ε) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζne : riemannZeta ((σ : ℂ) + ε) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [← hm_def] at hΦσ
    simp only [hH]
    rw [zetaResidueUnit_of_ne' hne1, hΦσ]
    push_cast at hC ⊢
    rw [hC]
    field_simp
    ring
  -- identity theorem
  set σ₀ : ℝ := 1 - ε / 2
  have hσ₀U : (σ₀ : ℂ) ∈ U := by
    simp only [hU_def, Set.mem_setOf_eq, Complex.ofReal_re, σ₀]; constructor <;> linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (σ₀ : ℂ), H z = 0 := by
    have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[≠] σ₀) (𝓝[≠] (σ₀ : ℂ)) :=
      Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
        fun σ hσ => by simpa using hσ
    have hev : ∀ᶠ σ : ℝ in 𝓝[≠] σ₀, H (σ : ℂ) = 0 := by
      have h1 : ∀ᶠ σ in 𝓝 σ₀, 1 - ε < σ ∧ σ < 1 :=
        (lt_mem_nhds (by simp only [σ₀]; linarith)).and (gt_mem_nhds (by simp only [σ₀]; linarith))
      filter_upwards [nhdsWithin_le_nhds h1] with σ hσ
      exact hzero σ hσ.1 hσ.2
    exact hmap.frequently hev.frequently
  have hEq := hHa.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hσ₀U hfreq
  have hs₀U : ρ - ε ∈ U := by
    simp only [hU_def, Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re]
    constructor <;> linarith
  have hval := hEq hs₀U
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hre1; exact lt_irrefl _ hre1
  simp only [hH, Pi.zero_apply] at hval
  rw [sub_add_cancel, zetaResidueUnit_of_ne' hρ1, hρ, mul_zero, zero_mul, zero_sub,
    neg_eq_zero] at hval
  exact (mul_eq_zero.mp hval).resolve_left (sub_ne_zero.mpr hρ1)

/-- **Subpower energy at every damping is RH.** -/
theorem riemannHypothesis_of_subpower_energy
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, hβ, hβ1⟩ := RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set w := ρ.re - 1 / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  set η := min w (1 / 2) with hη
  have hη0 : 0 < η := lt_min hw0 (by norm_num)
  -- every damping `ε ∈ (0, η)` translates `ρ` to a zero `ρ − ε`
  have htrans : ∀ ε : ℝ, 0 < ε → ε < η → riemannZeta (ρ - ε) = 0 := by
    intro ε hε hεη
    have hεw : ε < w := lt_of_lt_of_le hεη (min_le_left _ _)
    have hε2 : ε < 1 / 2 := lt_of_lt_of_le hεη (min_le_right _ _)
    obtain ⟨C, hC, hE⟩ := h ε hε hε2 (w - ε) (by linarith)
    exact riemannZeta_sub_eq_zero_of_energy_growth hε hC (by linarith) hE hζ (by linarith) hβ1
  -- these zeros accumulate at `ρ − η/2`
  set z₀ : ℂ := ρ - ((η / 2 : ℝ) : ℂ)
  have hev := RHTower.eventually_zetaResidueUnit_ne_zero z₀
  have hmap : Tendsto (fun ε : ℝ => ρ - (ε : ℂ)) (𝓝[≠] (η / 2)) (𝓝[≠] z₀) := by
    refine ((continuous_const.sub Complex.continuous_ofReal).continuousWithinAt).tendsto_nhdsWithin
      fun ε hε => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hε ⊢
    intro h
    exact hε (by exact_mod_cast sub_right_injective h)
  have hfreq : ∃ᶠ ε : ℝ in 𝓝[≠] (η / 2), RHTower.zetaResidueUnit (ρ - (ε : ℂ)) = 0 := by
    have h1 : ∀ᶠ ε in 𝓝 (η / 2), 0 < ε ∧ ε < η :=
      (lt_mem_nhds (by linarith)).and (gt_mem_nhds (by linarith))
    refine (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds h1] with ε hε
    have hne : ρ - (ε : ℂ) ≠ 1 := by
      intro h1'; have := congrArg Complex.re h1'; simp at this; linarith [hε.1]
    rw [zetaResidueUnit_of_ne' hne, htrans ε hε.1 hε.2, mul_zero]
  obtain ⟨z, hz1, hz2⟩ :=
    ((hmap.frequently (p := fun z => RHTower.zetaResidueUnit z = 0) hfreq).and_eventually hev).exists
  exact hz2 hz1
end GaloisForLFunctions.ArithmeticCorrelationGeometry
