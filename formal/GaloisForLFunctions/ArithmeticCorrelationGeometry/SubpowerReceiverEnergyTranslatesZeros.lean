import GaloisForLFunctions.ArithmeticCorrelationGeometry.ChargedBoundariesAreCriticalAtAQuarter
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.SignedModulusSumOfTheInteriorMartingale
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

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
    have hIcc : Ico (0 + 1) (n + 1) = Icc 1 n := by ext i; simp only [mem_Ico, mem_Icc]; omega
    rw [hIcc]
    exact hE n
  have hbound := fun N : ℕ => norm_sum_Ioc_mul_rpow_neg_le (c := fun i => ((e i : ℝ) : ℂ)) hC hκ hκγ
    hS 0 N
  refine summable_of_sum_range_le (fun n => mul_nonneg (he n) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (c := C * (2 + γ * 2 ^ (γ + 1) / (γ - κ)) * ((0 : ℝ) + 1) ^ (κ - γ)) fun N => ?_
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
  simp only [Pi.add_apply]
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
end GaloisForLFunctions.ArithmeticCorrelationGeometry
