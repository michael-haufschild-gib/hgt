import GaloisForLFunctions.HTGeometry.PrimeHodgeSteinGramian
import GaloisForLFunctions.HTGeometry.CayleyThetaRecordFlatness
import GaloisForLFunctions.HTGeometry.DigammaHorizontalVanishing
import GaloisForLFunctions.HTGeometry.IndexedDiagonalApproximation
import GaloisForLFunctions.RHTower.WeakSchattenResidue
import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation
import GaloisForLFunctions.RHTower.PositiveSchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.RHTower.IsometricSandwichApproxNumber
import GaloisForLFunctions.RHTower.SchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.HTGeometry.OperatorDeterminantSufficiency
import GaloisForLFunctions.HTGeometry.DeterminantCompletionNaturality
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.HTGeometry.NoncommutativeQubitResponsePolarization

/-!
# The prime–Hodge singular residue clock

For the forced survival shift `C e_k = √r_k e_{k+1}` on `ℓ²(ℕ)`, the elapsed-history defects
`D_N = I - C*ᴺ Cᴺ` are the positive compact diagonals

`d_{N,k} = 1 - m_{k+N}/m_k = A_N/(2k+2N+3) + B_N/(2k+2N+5) + C_N/(2k+2N+7)`,

`A_N = N(N-1)(N-2)`, `B_N = -2N(N-1)(N+1)`, `C_N = N(N+1)(N+2)`, strictly decreasing to zero.

* **(A)** `D_N ≥ 0` is compact and its approximation numbers are `d_{N,k}`.
* **(B)** `k d_{N,k} → 3N`: `D_N` is weak trace class, not trace class, in every `S_p`, `p > 1`,
with
  honest logarithmic residue `3N`.
* **(C)** `D_{N+M} = D_N + C*ᴺ D_M Cᴺ`; the exit currents `E_j = C*ʲ D_1 Cʲ = D_{j+1} - D_j` have
  residue `3` each and pairwise trace-class differences.
* **(D)** the finite part `FP(D_N) = lim (∑_{k<K} d_{N,k} - 3N log K)` exists and equals
  `-(A_N ψ(N+3/2) + B_N ψ(N+5/2) + C_N ψ(N+7/2))/2`; `FP(D_1) = -3ψ(9/2)`, and
  `FP(E_j) - FP(E_l) = Tr(E_j - E_l)`.
* **(PHSR.14)** `⟨e_0, E_j e_0⟩ = w_j = Tr(P_j 𝖳)`, summing to `1`.
* **(E)** on the prime-formed carrier `u_j = V e_j`, `𝒟_N = V D_N V*` and `𝖳` are diagonal with
  entries `d_{N,j}` and `w_j`; `𝒟_N + z𝖳` has residue `3N` and finite part `FP(D_N) + z`.
* **(F)** for a nonzero theta tilt the ratios `ρ_n = q_{n+1}/q_n` increase to one, and the theta
  hazard `diag(1 - ρ_n)` is positive compact with `(1/log N) ∑_{n<N} (1 - ρ_n) → ∞`: it is not
  weak trace class, so it differs from `D_1` by no trace-class operator.
-/

open MeasureTheory Filter Topology Set ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The elapsed-history defect -/

/-- The elapsed defect `d_{N,k} = 1 - m_{k+N}/m_k`. -/
def elapsedDefect (N k : ℕ) : ℝ := 1 - PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k

/-- The partial-fraction coefficients `A_N, B_N, C_N`. -/
def residueCoeffA (N : ℕ) : ℝ := N * ((N : ℝ) - 1) * ((N : ℝ) - 2)
def residueCoeffB (N : ℕ) : ℝ := -2 * N * ((N : ℝ) - 1) * ((N : ℝ) + 1)
def residueCoeffC (N : ℕ) : ℝ := N * ((N : ℝ) + 1) * ((N : ℝ) + 2)

theorem residueCoeff_sum (N : ℕ) :
    residueCoeffA N + residueCoeffB N + residueCoeffC N = 6 * N := by
  unfold residueCoeffA residueCoeffB residueCoeffC
  ring

/-- **(PHSR.2).**  `d_{N,k} = 1 - ∏_{a ∈ {3,5,7}} (2k+a)/(2k+2N+a)`. -/
theorem elapsedDefect_eq_prod (N k : ℕ) :
    elapsedDefect N k = 1 - (2 * (k : ℝ) + 3) / (2 * k + 2 * N + 3) *
      ((2 * (k : ℝ) + 5) / (2 * k + 2 * N + 5)) * ((2 * (k : ℝ) + 7) / (2 * k + 2 * N + 7)) := by
  rw [elapsedDefect, PrimeHodgeHistory.m, PrimeHodgeHistory.m]
  push_cast
  have h1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 2 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 7 := by positivity
  field_simp

/-- **(PHSR.13).**  The exact partial fractions of `d_{N,k}`. -/
theorem elapsedDefect_partialFraction (N k : ℕ) :
    elapsedDefect N k = residueCoeffA N / (2 * k + 2 * N + 3) +
      residueCoeffB N / (2 * k + 2 * N + 5) + residueCoeffC N / (2 * k + 2 * N + 7) := by
  rw [elapsedDefect_eq_prod]
  unfold residueCoeffA residueCoeffB residueCoeffC
  have h1 : (0 : ℝ) < 2 * k + 2 * N + 3 := by positivity
  have h2 : (0 : ℝ) < 2 * k + 2 * N + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 2 * N + 7 := by positivity
  field_simp
  ring

theorem survivalRemainderWeight_eq (N k : ℕ) :
    PrimeHodgeHistory.survivalRemainderWeight N k = PrimeHodgeHistory.m (k + N) /
      PrimeHodgeHistory.m k := rfl

theorem elapsedDefect_nonneg (N k : ℕ) : 0 ≤ elapsedDefect N k := by
  rw [elapsedDefect, sub_nonneg, ← survivalRemainderWeight_eq]
  exact PrimeHodgeHistory.survivalRemainderWeight_le_one N k

theorem elapsedDefect_le_one (N k : ℕ) : elapsedDefect N k ≤ 1 := by
  rw [elapsedDefect, sub_le_self_iff, ← survivalRemainderWeight_eq]
  exact PrimeHodgeHistory.survivalRemainderWeight_nonneg N k

/-- `d_{N,k} ≤ 3N/(k+1)`. -/
theorem elapsedDefect_le (N k : ℕ) : elapsedDefect N k ≤ 3 * N / ((k : ℝ) + 1) := by
  rw [elapsedDefect_eq_prod]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set x := 2 * (N : ℝ) / (2 * k + 2 * N + 3)
  set y := 2 * (N : ℝ) / (2 * k + 2 * N + 5)
  set z := 2 * (N : ℝ) / (2 * k + 2 * N + 7)
  have hx : (2 * (k : ℝ) + 3) / (2 * k + 2 * N + 3) = 1 - x := by
    have : (0 : ℝ) < 2 * k + 2 * N + 3 := by positivity
    simp only [x]
    field_simp
    ring
  have hy : (2 * (k : ℝ) + 5) / (2 * k + 2 * N + 5) = 1 - y := by
    have : (0 : ℝ) < 2 * k + 2 * N + 5 := by positivity
    simp only [y]
    field_simp
    ring
  have hz : (2 * (k : ℝ) + 7) / (2 * k + 2 * N + 7) = 1 - z := by
    have : (0 : ℝ) < 2 * k + 2 * N + 7 := by positivity
    simp only [z]
    field_simp
    ring
  rw [hx, hy, hz]
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hx1 : x ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hy1 : y ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hxb : x ≤ N / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hyb : y ≤ N / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hzb : z ≤ N / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hsum : 1 - (1 - x) * (1 - y) * (1 - z) ≤ x + y + z := by
    nlinarith [mul_nonneg hx0 hy0, mul_nonneg (mul_nonneg hx0 hy0) hz0, mul_nonneg hy0 hz0,
      mul_nonneg hx0 hz0, mul_le_mul_of_nonneg_left hz0 (mul_nonneg hx0 hy0)]
  calc 1 - (1 - x) * (1 - y) * (1 - z) ≤ x + y + z := hsum
    _ ≤ N / ((k : ℝ) + 1) + N / ((k : ℝ) + 1) + N / ((k : ℝ) + 1) := by linarith
    _ = 3 * N / ((k : ℝ) + 1) := by ring

theorem survivalRatio_prod_strictMono {N : ℕ} (hN : 1 ≤ N) :
    StrictMono fun k : ℕ => PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have e1 := elapsedDefect_eq_prod N k
  have e2 := elapsedDefect_eq_prod N (k + 1)
  rw [elapsedDefect] at e1 e2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlt : ∀ a : ℝ, 0 < a → (2 * (k : ℝ) + a) / (2 * k + 2 * N + a)
      < (2 * ((k + 1 : ℕ) : ℝ) + a) / (2 * ((k + 1 : ℕ) : ℝ) + 2 * N + a) := by
    intro a ha
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpos : ∀ a : ℝ, 0 < a → 0 < (2 * (k : ℝ) + a) / (2 * k + 2 * N + a) := fun a ha =>
    div_pos (by positivity) (by positivity)
  have hq : (2 * (k : ℝ) + 3) / (2 * k + 2 * N + 3) * ((2 * (k : ℝ) + 5) / (2 * k + 2 * N + 5))
        * ((2 * (k : ℝ) + 7) / (2 * k + 2 * N + 7))
      < (2 * ((k + 1 : ℕ) : ℝ) + 3) / (2 * ((k + 1 : ℕ) : ℝ) + 2 * N + 3)
        * ((2 * ((k + 1 : ℕ) : ℝ) + 5) / (2 * ((k + 1 : ℕ) : ℝ) + 2 * N + 5))
        * ((2 * ((k + 1 : ℕ) : ℝ) + 7) / (2 * ((k + 1 : ℕ) : ℝ) + 2 * N + 7)) := by
    have a3 := hlt 3 (by norm_num)
    have a5 := hlt 5 (by norm_num)
    have a7 := hlt 7 (by norm_num)
    have p3 := hpos 3 (by norm_num)
    have p5 := hpos 5 (by norm_num)
    have p7 := hpos 7 (by norm_num)
    have := mul_lt_mul'' (mul_lt_mul'' a3 a5 p3.le p5.le) a7 (mul_pos p3 p5).le p7.le
    exact this
  show PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k
    < PrimeHodgeHistory.m (k + 1 + N) / PrimeHodgeHistory.m (k + 1)
  linarith

/-- **Theorem PHSR-A.**  `d_{N,k}` is strictly decreasing in `k` for `N ≥ 1`. -/
theorem elapsedDefect_strictAnti {N : ℕ} (hN : 1 ≤ N) : StrictAnti (elapsedDefect N) :=
  fun a b hab => by
    rw [elapsedDefect, elapsedDefect]
    linarith [survivalRatio_prod_strictMono hN hab]

theorem elapsedDefect_pos {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 0 < elapsedDefect N k :=
  lt_of_le_of_lt (elapsedDefect_nonneg N (k + 1)) (elapsedDefect_strictAnti hN (Nat.lt_succ_self k))

theorem tendsto_elapsedDefect (N : ℕ) : Tendsto (elapsedDefect N) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => 3 * (N : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (3 * (N : ℝ)) |>.comp (tendsto_add_atTop_nat 1)
      |>.congr fun k => by simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (elapsedDefect_nonneg N)
    (elapsedDefect_le N)

theorem elapsedDefect_antitone (N : ℕ) : Antitone (elapsedDefect N) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    intro a b _
    simp [elapsedDefect, div_self (PrimeHodgeHistory.m_pos _).ne']
  · exact (elapsedDefect_strictAnti h).antitone

/-! ## The operator `D_N` -/

/-- The history line `ℓ²(ℕ)`. -/
abbrev HistoryLine := lp (fun _ : ℕ => ℂ) 2

/-- **(PHSR.1).**  The elapsed-history defect `D_N = I - C*ᴺ Cᴺ`. -/
def elapsedHistoryDefect (N : ℕ) : HistoryLine →L[ℂ] HistoryLine :=
  ContinuousLinearMap.id ℂ _ - adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L
    primeHodgeHistorySurvivalShift ^ N

theorem norm_elapsedDefect_le (N k : ℕ) : ‖((elapsedDefect N k : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (elapsedDefect_nonneg N k)]
  exact elapsedDefect_le_one N k

/-- **(PHSR.2).**  `D_N = diag(d_{N,k})`. -/
theorem elapsedHistoryDefect_eq_diagonal (N : ℕ) :
    elapsedHistoryDefect N = _root_.HTGeometry.ellTwoDiagonal
      (fun k => ((elapsedDefect N k : ℝ) : ℂ)) (norm_elapsedDefect_le N) := by
  ext f k
  rw [elapsedHistoryDefect, sub_apply, id_apply, adjoint_survivalShift_pow_comp, lp.coeFn_sub,
    Pi.sub_apply, primeHodgeHistorySurvivalRemainder, _root_.HTGeometry.ellTwoDiagonal_apply,
    _root_.HTGeometry.ellTwoDiagonal_apply, elapsedDefect, survivalRemainderWeight_eq]
  push_cast
  ring

theorem elapsedHistoryDefect_coord (N : ℕ) (f : HistoryLine) (k : ℕ) :
    (elapsedHistoryDefect N f : ℕ → ℂ) k = (elapsedDefect N k : ℂ) * (f : ℕ → ℂ) k := by
  rw [elapsedHistoryDefect_eq_diagonal, _root_.HTGeometry.ellTwoDiagonal_apply]

theorem elapsedHistoryDefect_basis (N k : ℕ) :
    elapsedHistoryDefect N (historyCoord k) = ((elapsedDefect N k : ℝ) : ℂ) • historyCoord k := by
  rw [elapsedHistoryDefect_eq_diagonal]
  exact diagonal_historyCoord _ _ k

/-- **Theorem PHSR-A.**  `D_N ≥ 0`. -/
theorem elapsedHistoryDefect_isPositive (N : ℕ) : (elapsedHistoryDefect N).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hval : ⟪elapsedHistoryDefect N x, x⟫_ℂ
      = (((‖x‖ ^ 2 - ‖(primeHodgeHistorySurvivalShift ^ N) x‖ ^ 2 : ℝ)) : ℂ) := by
    rw [elapsedHistoryDefect, sub_apply, id_apply, inner_sub_left, comp_apply,
      adjoint_inner_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    push_cast
    simp
  rw [hval]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨trivial, ?_⟩
  have := norm_survivalShift_pow_apply_le N x
  nlinarith [norm_nonneg ((primeHodgeHistorySurvivalShift ^ N) x)]

/-- **Theorem PHSR-A.**  `D_N` is compact. -/
theorem isCompactOperator_elapsedHistoryDefect (N : ℕ) :
    IsCompactOperator (elapsedHistoryDefect N) := by
  refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
    (c := fun k => ((elapsedDefect N k : ℝ) : ℂ)) (elapsedHistoryDefect_basis N) ?_
  rw [Nat.cofinite_eq_atTop]
  simpa [Real.norm_eq_abs, abs_of_nonneg (elapsedDefect_nonneg N _)] using
    (tendsto_elapsedDefect N).norm

/-- **Theorem PHSR-A.**  The approximation numbers of `D_N` are `d_{N,k}`. -/
theorem approxNumber_elapsedHistoryDefect (N n : ℕ) :
    approxNumber (elapsedHistoryDefect N) n = elapsedDefect N n := by
  rw [elapsedHistoryDefect_eq_diagonal]
  exact _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq (Equiv.refl ℕ)
    (lam := fun k => ((elapsedDefect N k : ℝ) : ℂ)) (r := elapsedDefect N)
    (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (elapsedDefect_nonneg N i)]
      rfl)
    (elapsedDefect_nonneg N) (fun h => elapsedDefect_antitone N h) n

/-- **Theorem PHSR-B.**  `D_N` is weak trace class: `d_{N,k} ≤ 3N/(k+1)`. -/
theorem memWeakSchattenClass_elapsedHistoryDefect (N : ℕ) :
    MemWeakSchattenClass 1 (elapsedHistoryDefect N) :=
  ⟨3 * N, by positivity, fun n => by
    rw [Real.rpow_one, approxNumber_elapsedHistoryDefect]
    exact elapsedDefect_le N n⟩

/-! ## The digamma finite part -/

theorem sum_inv_add_eq_digamma {c : ℂ} (hc : 0 < c.re) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℂ) + c)⁻¹
      = Complex.digamma (c + K) - Complex.digamma c := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hs : ∀ m : ℕ, c + (K : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at this
      have h1 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [Finset.sum_range_succ, ih, Nat.cast_succ, ← add_assoc,
      Complex.digamma_apply_add_one _ hs, add_comm (K : ℂ) c]
    ring

theorem tendsto_digamma_add_nat_sub_log {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun K : ℕ => Complex.digamma (c + K) - Complex.log (K : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_digamma_sub_log_horizontal hc).add (tendsto_log_add_nat_sub_log c)
  rw [add_zero] at h
  refine h.congr fun K => ?_
  ring

/-- The shifted digamma arguments `N + a/2`. -/
def residueShift (N : ℕ) (a : ℝ) : ℂ := (N : ℂ) + ((a / 2 : ℝ) : ℂ)

theorem residueShift_re_pos (N : ℕ) {a : ℝ} (ha : 0 < a) : 0 < (residueShift N a).re := by
  simp only [residueShift, Complex.add_re, Complex.natCast_re, Complex.ofReal_re]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem inv_two_mul_add (N k : ℕ) (a : ℝ) :
    ((1 / (2 * (k : ℝ) + 2 * N + a) : ℝ) : ℂ) = 1 / 2 * ((k : ℂ) + residueShift N a)⁻¹ := by
  rw [residueShift]
  push_cast
  rw [show (2 * (k : ℂ) + 2 * N + a) = 2 * ((k : ℂ) + (N + a / 2)) by ring]
  rw [one_div, mul_inv, one_div]

/-- **(PHSR.13)**, summed: `∑_{k<K} d_{N,k} = ½ ∑_a c_a (ψ(N + a/2 + K) - ψ(N + a/2))`. -/
theorem sum_elapsedDefect_eq_digamma (N K : ℕ) :
    ((∑ k ∈ Finset.range K, elapsedDefect N k : ℝ) : ℂ)
      = 1 / 2 * ((residueCoeffA N : ℂ) * (Complex.digamma (residueShift N 3 + K)
            - Complex.digamma (residueShift N 3))
          + (residueCoeffB N : ℂ) * (Complex.digamma (residueShift N 5 + K)
            - Complex.digamma (residueShift N 5))
          + (residueCoeffC N : ℂ) * (Complex.digamma (residueShift N 7 + K)
            - Complex.digamma (residueShift N 7))) := by
  rw [← sum_inv_add_eq_digamma (residueShift_re_pos N (by norm_num : (0 : ℝ) < 3)),
    ← sum_inv_add_eq_digamma (residueShift_re_pos N (by norm_num : (0 : ℝ) < 5)),
    ← sum_inv_add_eq_digamma (residueShift_re_pos N (by norm_num : (0 : ℝ) < 7))]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [elapsedDefect_partialFraction]
  have e3 := inv_two_mul_add N k 3
  have e5 := inv_two_mul_add N k 5
  have e7 := inv_two_mul_add N k 7
  push_cast at e3 e5 e7 ⊢
  rw [div_eq_mul_one_div (residueCoeffA N : ℂ), div_eq_mul_one_div (residueCoeffB N : ℂ),
    div_eq_mul_one_div (residueCoeffC N : ℂ), e3, e5, e7]
  ring

/-- **(PHSR.10).**  The canonical source finite part
`FP(D_N) = -(A_N ψ(N+3/2) + B_N ψ(N+5/2) + C_N ψ(N+7/2))/2`. -/
def elapsedFinitePart (N : ℕ) : ℂ :=
  -(1 / 2) * ((residueCoeffA N : ℂ) * Complex.digamma (residueShift N 3)
    + (residueCoeffB N : ℂ) * Complex.digamma (residueShift N 5)
    + (residueCoeffC N : ℂ) * Complex.digamma (residueShift N 7))

/-- **Theorem PHSR-D.**  `∑_{k<K} d_{N,k} - 3N log K → FP(D_N)`. -/
theorem tendsto_sum_elapsedDefect_sub_log (N : ℕ) :
    Tendsto (fun K : ℕ => ((∑ k ∈ Finset.range K, elapsedDefect N k
      - 3 * N * Real.log K : ℝ) : ℂ)) atTop (𝓝 (elapsedFinitePart N)) := by
  have h3 := tendsto_digamma_add_nat_sub_log (residueShift_re_pos N (by norm_num : (0 : ℝ) < 3))
  have h5 := tendsto_digamma_add_nat_sub_log (residueShift_re_pos N (by norm_num : (0 : ℝ) < 5))
  have h7 := tendsto_digamma_add_nat_sub_log (residueShift_re_pos N (by norm_num : (0 : ℝ) < 7))
  have hlim := ((((h3.const_mul (residueCoeffA N : ℂ)).add (h5.const_mul (residueCoeffB N : ℂ))).add
    (h7.const_mul (residueCoeffC N : ℂ))).const_mul (1 / 2 : ℂ)).add
      (tendsto_const_nhds (x := elapsedFinitePart N))
  simp only [mul_zero, add_zero, zero_add] at hlim
  refine hlim.congr fun K => ?_
  have hsum := residueCoeff_sum N
  have hlog : ((Real.log K : ℝ) : ℂ) = Complex.log (K : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg K)]
    push_cast
    rfl
  rw [Complex.ofReal_sub, sum_elapsedDefect_eq_digamma, Complex.ofReal_mul, hlog,
    elapsedFinitePart]
  have hsumC : (residueCoeffA N : ℂ) + (residueCoeffB N : ℂ) + (residueCoeffC N : ℂ)
      = 6 * (N : ℂ) := by exact_mod_cast hsum
  push_cast
  linear_combination (-(1 / 2) : ℂ) * Complex.log (K : ℂ) * hsumC

theorem elapsedFinitePart_im (N : ℕ) : (elapsedFinitePart N).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_sum_elapsedDefect_sub_log N)
  simp only [Function.comp_def, Complex.ofReal_im] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **Theorem PHSR-D, real form.** -/
theorem tendsto_sum_elapsedDefect_sub_log_real (N : ℕ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, elapsedDefect N k - 3 * N * Real.log K) atTop
      (𝓝 (elapsedFinitePart N).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sum_elapsedDefect_sub_log N)
  exact h.congr fun K => by simp only [Function.comp_apply, Complex.ofReal_re]

/-- **(PHSR.11).**  `FP(D_1) = -3 ψ(9/2)`. -/
theorem elapsedFinitePart_one : elapsedFinitePart 1 = -3 * Complex.digamma (9 / 2) := by
  simp only [elapsedFinitePart, residueCoeffA, residueCoeffB, residueCoeffC, residueShift]
  push_cast
  norm_num
  ring

theorem tendsto_log_succ_sub_log :
    Tendsto (fun K : ℕ => Real.log ((K : ℝ) + 1) - Real.log K) atTop (𝓝 0) := by
  have h : Tendsto (fun K : ℕ => Real.log (1 + 1 / (K : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => 1 + 1 / (K : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat 1)
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    exact this
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [← Real.log_div (by positivity) hK'.ne']
  congr 1
  field_simp

/-- **Theorem PHSR-B.**  `D_N` has honest logarithmic residue `3N`. -/
theorem hasSchattenLogResidue_elapsedHistoryDefect (N : ℕ) :
    HasSchattenLogResidue 1 (elapsedHistoryDefect N) (3 * N) := by
  have hpart : ∀ K, schattenPowerPartialSum 1 (elapsedHistoryDefect N) K
      = ∑ k ∈ Finset.range K, elapsedDefect N k := fun K => by
    rw [schattenPowerPartialSum]
    exact Finset.sum_congr rfl fun k _ => by rw [Real.rpow_one, approxNumber_elapsedHistoryDefect]
  unfold HasSchattenLogResidue
  simp_rw [hpart]
  have hF := tendsto_sum_elapsedDefect_sub_log_real N
  have hshift := hF.sub (tendsto_log_succ_sub_log.const_mul (3 * (N : ℝ)))
  rw [mul_zero, sub_zero] at hshift
  have hlog : Tendsto (fun K : ℕ => Real.log ((K : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hdiv := hshift.div_atTop hlog
  have h2 := hdiv.add (tendsto_const_nhds (x := 3 * (N : ℝ)))
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hpos : 0 < Real.log ((K : ℝ) + 1) := Real.log_pos (by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith)
  field_simp
  ring

/-- **Theorem PHSR-B.**  For `N ≥ 1`, `D_N` is not trace class but lies in every `S_p`, `p > 1`. -/
theorem elapsedHistoryDefect_schatten {N : ℕ} (hN : 1 ≤ N) :
    ¬MemSchattenClass 1 (elapsedHistoryDefect N) ∧
      ∀ p : ℝ, 1 < p → MemSchattenClass p (elapsedHistoryDefect N) := by
  refine ⟨(hasSchattenLogResidue_elapsedHistoryDefect N).not_memSchattenClass (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity), fun p hp => ?_⟩
  exact (memWeakSchattenClass_elapsedHistoryDefect N).memSchattenClass_of_lt one_pos hp

/-- **(PHSR.3).**  `k d_{N,k} → 3N`. -/
theorem tendsto_mul_elapsedDefect (N : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ) * elapsedDefect N k) atTop (𝓝 (3 * N)) := by
  have hterm : ∀ a : ℝ, 0 < a → Tendsto (fun k : ℕ => (k : ℝ) / (2 * k + 2 * N + a)) atTop
      (𝓝 (1 / 2)) := by
    intro a ha
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (2 * (N : ℝ) + a)).const_add 2).inv₀
      (by norm_num : (2 : ℝ) + 0 ≠ 0)
    rw [add_zero] at h
    rw [one_div]
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
    ring
  have h := (((hterm 3 (by norm_num)).const_mul (residueCoeffA N)).add
    ((hterm 5 (by norm_num)).const_mul (residueCoeffB N))).add
      ((hterm 7 (by norm_num)).const_mul (residueCoeffC N))
  have hlim : residueCoeffA N * (1 / 2) + residueCoeffB N * (1 / 2) + residueCoeffC N * (1 / 2)
      = 3 * N := by linarith [residueCoeff_sum N]
  rw [hlim] at h
  refine h.congr fun k => ?_
  rw [elapsedDefect_partialFraction]
  ring


/-! ## Diagonal operators in the history basis -/

theorem eq_diagonal_of_basis {A : HistoryLine →L[ℂ] HistoryLine} (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ i, ‖lam i‖ ≤ C) (hA : ∀ k, A (historyCoord k) = lam k • historyCoord k) :
    A = _root_.HTGeometry.ellTwoDiagonal lam hC :=
  historyCoord_ext fun i k => by
    rw [hA, inner_diagonal_historyCoord, inner_smul_right, inner_historyCoord]
    split_ifs <;> simp

/-- A real nonnegative diagonal is a positive operator. -/
theorem isPositive_ellTwoDiagonal_ofReal (r : ℕ → ℝ) {C : ℝ} (hC : ∀ n, ‖((r n : ℝ) : ℂ)‖ ≤ C)
    (hr : ∀ n, 0 ≤ r n) :
    (_root_.HTGeometry.ellTwoDiagonal (fun n => ((r n : ℝ) : ℂ)) hC).IsPositive := by
  have heq : _root_.HTGeometry.ellTwoDiagonal (fun n => ((r n : ℝ) : ℂ)) hC
      = _root_.RHTower.diagonalOperator (fun n => ((r n : ℝ) : ℂ)) hC := by
    ext f n
    simp [_root_.HTGeometry.ellTwoDiagonal_apply, _root_.RHTower.diagonalOperator_apply]
  rw [heq]
  exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal r hC hr

/-! ## The cocycle and the exit currents -/

theorem elapsedHistoryDefect_zero : elapsedHistoryDefect 0 = 0 := by
  ext f k
  simp [elapsedHistoryDefect_coord, elapsedDefect, div_self (PrimeHodgeHistory.m_pos k).ne']

/-- **Theorem PHSR-C, (PHSR.6).**  `D_{N+M} = D_N + C*ᴺ D_M Cᴺ`. -/
theorem elapsedHistoryDefect_add (N M : ℕ) :
    elapsedHistoryDefect (N + M) = elapsedHistoryDefect N +
      adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L elapsedHistoryDefect M ∘L
        primeHodgeHistorySurvivalShift ^ N := by
  simp only [elapsedHistoryDefect]
  rw [add_comm N M, pow_add, mul_def, adjoint_comp]
  simp only [comp_sub, sub_comp, id_comp, comp_assoc]
  abel

/-- **(PHSR.5).**  The exit current `E_j = C*ʲ D_1 Cʲ`. -/
def exitCurrent (j : ℕ) : HistoryLine →L[ℂ] HistoryLine :=
  adjoint (primeHodgeHistorySurvivalShift ^ j) ∘L elapsedHistoryDefect 1 ∘L
    primeHodgeHistorySurvivalShift ^ j

/-- **(PHSR.7).**  `E_j = D_{j+1} - D_j`. -/
theorem exitCurrent_eq_sub (j : ℕ) :
    exitCurrent j = elapsedHistoryDefect (j + 1) - elapsedHistoryDefect j := by
  rw [elapsedHistoryDefect_add j 1, exitCurrent, add_sub_cancel_left]

/-- **(PHSR.7).**  `D_N = ∑_{j<N} E_j`. -/
theorem elapsedHistoryDefect_eq_sum (N : ℕ) :
    elapsedHistoryDefect N = ∑ j ∈ Finset.range N, exitCurrent j := by
  induction N with
  | zero => rw [elapsedHistoryDefect_zero, Finset.sum_range_zero]
  | succ n ih => rw [Finset.sum_range_succ, ← ih, exitCurrent_eq_sub, add_sub_cancel]

theorem exitCurrent_zero : exitCurrent 0 = elapsedHistoryDefect 1 := by
  rw [exitCurrent_eq_sub, elapsedHistoryDefect_zero, sub_zero]

theorem elapsedHistoryDefect_one : elapsedHistoryDefect 1 = primeHodgeHistoryExitDefect := by
  ext f k
  rw [elapsedHistoryDefect_coord, primeHodgeHistoryExitDefect,
    _root_.HTGeometry.ellTwoDiagonal_apply]
  rfl

/-- **(PHSR.8).**  `E_j = diag(w_{k+j}/m_k)`. -/
theorem exitCurrent_eq_exitRecordAt (j : ℕ) :
    exitCurrent j = primeHodgeHistoryExitRecordAt j := by
  rw [exitCurrent, elapsedHistoryDefect_one, adjoint_survivalShift_pow_exitDefect]

theorem exitCurrent_basis (j k : ℕ) :
    exitCurrent j (historyCoord k)
      = ((PrimeHodgeHistory.conditionalExitWeight j k : ℝ) : ℂ) • historyCoord k := by
  rw [exitCurrent_eq_exitRecordAt, primeHodgeHistoryExitRecordAt]
  exact diagonal_historyCoord _ _ k

theorem conditionalExitWeight_eq (j k : ℕ) :
    PrimeHodgeHistory.conditionalExitWeight j k
      = elapsedDefect (j + 1) k - elapsedDefect j k := by
  rw [PrimeHodgeHistory.conditionalExitWeight, PrimeHodgeHistory.w, elapsedDefect, elapsedDefect,
    ← add_assoc]
  ring

/-- **(PHSR.8).**  `k w_{k+j}/m_k → 3`. -/
theorem tendsto_mul_conditionalExitWeight (j : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ) * PrimeHodgeHistory.conditionalExitWeight j k) atTop
      (𝓝 3) := by
  have h := (tendsto_mul_elapsedDefect (j + 1)).sub (tendsto_mul_elapsedDefect j)
  have e : 3 * ((j + 1 : ℕ) : ℝ) - 3 * (j : ℝ) = 3 := by push_cast; ring
  rw [e] at h
  refine h.congr fun k => ?_
  rw [conditionalExitWeight_eq]
  ring

theorem exitCurrent_isPositive (j : ℕ) : (exitCurrent j).IsPositive :=
  (elapsedHistoryDefect_isPositive 1).adjoint_conj _

theorem isCompactOperator_exitCurrent (j : ℕ) : IsCompactOperator (exitCurrent j) := by
  rw [exitCurrent_eq_sub]
  exact (isCompactOperator_elapsedHistoryDefect _).sub (isCompactOperator_elapsedHistoryDefect _)

theorem isCompactOperator_exitCurrent_sub (j l : ℕ) :
    IsCompactOperator (exitCurrent j - exitCurrent l) :=
  (isCompactOperator_exitCurrent j).sub (isCompactOperator_exitCurrent l)

/-- `E_{i+1} - E_i = C*ⁱ (E_1 - E_0) Cⁱ`. -/
theorem exitCurrent_succ_sub (i : ℕ) :
    exitCurrent (i + 1) - exitCurrent i = adjoint (primeHodgeHistorySurvivalShift ^ i) ∘L
      (exitCurrent 1 - exitCurrent 0) ∘L primeHodgeHistorySurvivalShift ^ i := by
  have h2 : elapsedHistoryDefect (i + 1 + 1) = elapsedHistoryDefect i +
      adjoint (primeHodgeHistorySurvivalShift ^ i) ∘L elapsedHistoryDefect 2 ∘L
        primeHodgeHistorySurvivalShift ^ i := elapsedHistoryDefect_add i 2
  have h1 := elapsedHistoryDefect_add i 1
  have e1 : exitCurrent 1 = elapsedHistoryDefect 2 - elapsedHistoryDefect 1 := exitCurrent_eq_sub 1
  rw [exitCurrent_eq_sub (i + 1), exitCurrent_eq_sub i, h2, h1, e1, exitCurrent_zero]
  simp only [comp_sub, sub_comp]
  abel

/-- The exit curvature `48/((2k+9)(2k+11))`. -/
def exitCurvature (k : ℕ) : ℝ := 48 / ((2 * (k : ℝ) + 9) * (2 * k + 11))

theorem exitCurvature_pos (k : ℕ) : 0 < exitCurvature k := by
  unfold exitCurvature
  positivity

theorem exitCurvature_eq (k : ℕ) :
    exitCurvature k = 2 * elapsedDefect 1 k - elapsedDefect 2 k - elapsedDefect 0 k := by
  rw [elapsedDefect_eq_prod, elapsedDefect_eq_prod, elapsedDefect_eq_prod, exitCurvature]
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h5 : (0 : ℝ) < 2 * k + 5 := by positivity
  have h7 : (0 : ℝ) < 2 * k + 7 := by positivity
  have h9 : (0 : ℝ) < 2 * k + 9 := by positivity
  have h11 : (0 : ℝ) < 2 * k + 11 := by positivity
  push_cast
  field_simp
  ring

theorem norm_exitCurvature_le (k : ℕ) : ‖((exitCurvature k : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exitCurvature_pos k), exitCurvature,
    div_le_one (by positivity)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem exitCurrent_zero_sub_one_basis (k : ℕ) :
    (exitCurrent 0 - exitCurrent 1) (historyCoord k)
      = ((exitCurvature k : ℝ) : ℂ) • historyCoord k := by
  have e0 : PrimeHodgeHistory.conditionalExitWeight 0 k = elapsedDefect 1 k - elapsedDefect 0 k :=
    conditionalExitWeight_eq 0 k
  have e1 : PrimeHodgeHistory.conditionalExitWeight 1 k = elapsedDefect 2 k - elapsedDefect 1 k :=
    conditionalExitWeight_eq 1 k
  rw [sub_apply, exitCurrent_basis, exitCurrent_basis, ← sub_smul, e0, e1, exitCurvature_eq]
  congr 1
  push_cast
  ring

/-- `E_0 - E_1 = diag(48/((2k+9)(2k+11)))`. -/
theorem exitCurrent_zero_sub_one_eq : exitCurrent 0 - exitCurrent 1
    = _root_.HTGeometry.ellTwoDiagonal (fun k => ((exitCurvature k : ℝ) : ℂ))
      norm_exitCurvature_le :=
  eq_diagonal_of_basis _ _ exitCurrent_zero_sub_one_basis

/-- `∑_k 48/((2k+9)(2k+11)) = 8/3`. -/
theorem hasSum_exitCurvature : HasSum exitCurvature (8 / 3) := by
  have htel : ∀ k : ℕ, exitCurvature k
      = 24 / (2 * (k : ℝ) + 9) - 24 / (2 * ((k + 1 : ℕ) : ℝ) + 9) := fun k => by
    have h9 : (0 : ℝ) < 2 * k + 9 := by positivity
    have h11 : (0 : ℝ) < 2 * k + 11 := by positivity
    rw [exitCurvature]
    push_cast
    field_simp
    ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (exitCurvature_pos k).le)]
  have hsum : ∀ K : ℕ, ∑ k ∈ Finset.range K, exitCurvature k
      = 24 / (2 * ((0 : ℕ) : ℝ) + 9) - 24 / (2 * (K : ℝ) + 9) := fun K => by
    simp_rw [htel]
    exact Finset.sum_range_sub' (fun k : ℕ => 24 / (2 * (k : ℝ) + 9)) K
  simp_rw [hsum]
  have hlim : Tendsto (fun K : ℕ => 24 / (2 * (K : ℝ) + 9)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 9
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
  have h := hlim.const_sub (24 / (2 * ((0 : ℕ) : ℝ) + 9))
  norm_num at h ⊢
  exact h

theorem exitCurrent_zero_sub_one_traceClass :
    MemSchattenClass 1 (exitCurrent 0 - exitCurrent 1) := by
  refine memSchattenClass_one_of_isPositive_of_summable_diagonal historyCoord ?_ ?_
  · rw [exitCurrent_zero_sub_one_eq]
    exact isPositive_ellTwoDiagonal_ofReal _ _ fun k => (exitCurvature_pos k).le
  · refine (Complex.summable_ofReal.mpr hasSum_exitCurvature.summable).congr fun k => ?_
    rw [exitCurrent_zero_sub_one_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one]

/-- `Tr(E_0 - E_1) = 8/3`. -/
theorem opTrace_exitCurrent_zero_sub_one :
    opTrace (exitCurrent 0 - exitCurrent 1) = ((8 / 3 : ℝ) : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one exitCurrent_zero_sub_one_traceClass
    historyCoord]
  rw [← (Complex.hasSum_ofReal.mpr hasSum_exitCurvature).tsum_eq]
  refine tsum_congr fun k => ?_
  rw [exitCurrent_zero_sub_one_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one]

theorem memSchattenClass_one_zero_op : MemSchattenClass 1 (0 : HistoryLine →L[ℂ] HistoryLine) := by
  unfold MemSchattenClass
  simp [approxNumber_zero_op]

/-- **Theorem PHSR-C.**  `E_j - E_0` is trace class. -/
theorem exitCurrent_sub_zero_traceClass (j : ℕ) :
    MemSchattenClass 1 (exitCurrent j - exitCurrent 0) := by
  induction j with
  | zero => rw [sub_self]; exact memSchattenClass_one_zero_op
  | succ i ih =>
    have hsplit : exitCurrent (i + 1) - exitCurrent 0
        = (exitCurrent (i + 1) - exitCurrent i) + (exitCurrent i - exitCurrent 0) := by abel
    rw [hsplit]
    have h10 : MemSchattenClass 1 (exitCurrent 1 - exitCurrent 0) := by
      have := memSchattenClass_neg exitCurrent_zero_sub_one_traceClass
      rwa [neg_sub] at this
    have hstep : MemSchattenClass 1 (exitCurrent (i + 1) - exitCurrent i) := by
      rw [exitCurrent_succ_sub]
      exact memSchattenClass_comp_left one_pos (memSchattenClass_comp_right one_pos h10)
    exact memSchattenClass_one_add (isCompactOperator_exitCurrent_sub _ _)
      (isCompactOperator_exitCurrent_sub _ _) hstep ih

/-- **Theorem PHSR-C.**  Every `E_j - E_l` is trace class. -/
theorem exitCurrent_sub_traceClass (j l : ℕ) :
    MemSchattenClass 1 (exitCurrent j - exitCurrent l) := by
  have h : exitCurrent j - exitCurrent l
      = (exitCurrent j - exitCurrent 0) + -(exitCurrent l - exitCurrent 0) := by abel
  rw [h]
  exact memSchattenClass_one_add (isCompactOperator_exitCurrent_sub j 0)
    (isCompactOperator_exitCurrent_sub l 0).neg
    (exitCurrent_sub_zero_traceClass j) (memSchattenClass_neg (exitCurrent_sub_zero_traceClass l))

/-- **Theorem PHSR-C, (PHSR.7).**  Every exit current is weak trace class with honest logarithmic
residue `3`. -/
theorem exitCurrent_residue (j : ℕ) :
    MemWeakSchattenClass 1 (exitCurrent j) ∧ HasSchattenLogResidue 1 (exitCurrent j) 3 := by
  have hS := exitCurrent_sub_zero_traceClass j
  have h1 : HasSchattenLogResidue 1 (exitCurrent 0) 3 := by
    rw [exitCurrent_zero]
    simpa using hasSchattenLogResidue_elapsedHistoryDefect 1
  refine ⟨(memWeakSchattenClass_one_iff_of_memSchattenClass_one_sub hS).2 ?_,
    (hasSchattenLogResidue_one_iff_of_traceClass_sub (isCompactOperator_exitCurrent j)
      (isCompactOperator_exitCurrent 0) hS 3).2 h1⟩
  rw [exitCurrent_zero]
  exact memWeakSchattenClass_elapsedHistoryDefect 1

/-! ## Finite parts of the exit currents -/

theorem inner_exitCurrent_basis (j k : ℕ) :
    ⟪historyCoord k, exitCurrent j (historyCoord k)⟫_ℂ
      = ((elapsedDefect (j + 1) k - elapsedDefect j k : ℝ) : ℂ) := by
  rw [exitCurrent_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one,
    conditionalExitWeight_eq]

/-- **(PHSR.12).**  `∑_{k<K} ⟨e_k, E_j e_k⟩ - 3 log K → FP(D_{j+1}) - FP(D_j)`. -/
theorem tendsto_sum_exitCurrent_sub_log (j : ℕ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, ⟪historyCoord k, exitCurrent j (historyCoord k)⟫_ℂ
      - 3 * (Real.log K : ℂ)) atTop
      (𝓝 (elapsedFinitePart (j + 1) - elapsedFinitePart j)) := by
  have h := (tendsto_sum_elapsedDefect_sub_log (j + 1)).sub (tendsto_sum_elapsedDefect_sub_log j)
  simp_rw [inner_exitCurrent_basis]
  refine h.congr fun K => ?_
  push_cast
  rw [Finset.sum_sub_distrib]
  ring

/-- **(PHSR.12).**  `FP(E_j) - FP(E_l) = Tr(E_j - E_l)`. -/
theorem exitCurrent_finitePart_sub_eq_opTrace (j l : ℕ) :
    (elapsedFinitePart (j + 1) - elapsedFinitePart j)
        - (elapsedFinitePart (l + 1) - elapsedFinitePart l)
      = opTrace (exitCurrent j - exitCurrent l) := by
  have hS := exitCurrent_sub_traceClass j l
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS historyCoord]
  have hlim := (hS.one_summable_inner_diag_basis historyCoord).hasSum.tendsto_sum_nat
  have h2 := (tendsto_sum_exitCurrent_sub_log j).sub (tendsto_sum_exitCurrent_sub_log l)
  refine tendsto_nhds_unique h2 (hlim.congr fun K => ?_)
  simp only [sub_apply, inner_sub_right, Finset.sum_sub_distrib]
  ring

/-- **(PHSR.14).**  `⟨e_0, E_j e_0⟩ = w_j`. -/
theorem inner_exitCurrent_initial (j : ℕ) :
    ⟪historyCoord 0, exitCurrent j (historyCoord 0)⟫_ℂ = (PrimeHodgeHistory.w j : ℂ) := by
  rw [exitCurrent_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one,
    PrimeHodgeHistory.conditionalExitWeight, zero_add, PrimeHodgeHistory.m_zero, div_one]

/-- **(PHSR.14).**  `∑_j ⟨e_0, E_j e_0⟩ = 1`. -/
theorem hasSum_inner_exitCurrent_initial :
    HasSum (fun j => ⟪historyCoord 0, exitCurrent j (historyCoord 0)⟫_ℂ) 1 := by
  simp_rw [inner_exitCurrent_initial]
  simpa using Complex.hasSum_ofReal.mpr PrimeHodgeHistory.hasSum_w

section GradeTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem summable_gradeRecord (e : ℕ → E) (j : ℕ) :
    Summable fun n => ‖(if n = j then e n else 0 : E)‖ ^ 2 :=
  summable_of_ne_finset_zero (s := {j}) fun b hb => by
    rw [Finset.mem_singleton] at hb
    rw [if_neg hb, norm_zero, zero_pow two_ne_zero]

/-- `P_j 𝖳` is the record operator of the single grade `j`. -/
theorem historyGrade_comp_recordOp (e : ℕ → E) (he : Summable fun n => ‖e n‖ ^ 2) (j : ℕ) :
    historyGrade j ∘L recordOp e he
      = recordOp (fun n => if n = j then e n else 0) (summable_gradeRecord e j) := by
  ext f n
  rw [comp_apply, historyGrade_apply, recordOp_apply, lp.single_apply]
  by_cases h : n = j
  · subst h
    simp [recordOp_apply]
  · simp [h, recordOp_apply]

/-- `Tr(P_j 𝖳) = ‖e_j‖²`. -/
theorem opTrace_historyGrade_recordOp (e : ℕ → E) (he : Summable fun n => ‖e n‖ ^ 2) (j : ℕ) :
    opTrace (historyGrade j ∘L recordOp e he) = ((‖e j‖ ^ 2 : ℝ) : ℂ) := by
  rw [historyGrade_comp_recordOp, (recordOp_traceClass _ _).2.2, tsum_eq_single j fun b hb => by
    rw [if_neg hb, norm_zero, zero_pow two_ne_zero], if_pos rfl]

end GradeTrace

/-- **(PHSR.14).**  `⟨e_0, E_j e_0⟩ = w_j = Tr(P_j 𝖳)`. -/
theorem inner_exitCurrent_initial_eq_opTrace (j : ℕ) :
    ⟪historyCoord 0, exitCurrent j (historyCoord 0)⟫_ℂ
      = opTrace (historyGrade j ∘L hodgeCollisionRecord) := by
  rw [inner_exitCurrent_initial, hodgeCollisionRecord, collisionRecord,
    opTrace_historyGrade_recordOp, norm_hodgeExitVector_sq]

/-! ## Isometric transport of singular data -/

section IsometricTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- `a_n(A S B) ≤ ‖A‖ ‖B‖ a_n(S)` across two Hilbert spaces. -/
theorem approxNumber_sandwich_le (A : K →L[ℂ] H) (S : K →L[ℂ] K) (B : H →L[ℂ] K) (n : ℕ) :
    approxNumber (A ∘L S ∘L B) n ≤ ‖A‖ * ‖B‖ * approxNumber S n := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < ‖A‖ * ‖B‖ + 1 := by positivity
  obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt S n
    (lt_add_of_pos_right _ (div_pos hε hc))
  have hrank : HasRankLE (A ∘L F ∘L B) n := by
    obtain ⟨V, hfd, hle, hmem⟩ := hF
    haveI : Module.Finite ℂ (V.map (A : K →ₗ[ℂ] H)) := Module.Finite.map V _
    exact ⟨V.map (A : K →ₗ[ℂ] H), inferInstance, (Submodule.finrank_map_le _ V).trans hle,
      fun x => Submodule.mem_map_of_mem (hmem (B x))⟩
  have h1 := approxNumber_le (A ∘L S ∘L B) n _ hrank
  have h2 : A ∘L S ∘L B - A ∘L F ∘L B = A ∘L (S - F) ∘L B := by
    rw [sub_comp, comp_sub]
  have h3 : ‖A ∘L (S - F) ∘L B‖ ≤ ‖A‖ * ‖B‖ * ‖S - F‖ :=
    calc ‖A ∘L (S - F) ∘L B‖ ≤ ‖A‖ * ‖(S - F) ∘L B‖ := opNorm_comp_le _ _
      _ ≤ ‖A‖ * (‖S - F‖ * ‖B‖) := by gcongr; exact opNorm_comp_le _ _
      _ = ‖A‖ * ‖B‖ * ‖S - F‖ := by ring
  rw [h2] at h1
  have hAB : 0 ≤ ‖A‖ * ‖B‖ := by positivity
  calc approxNumber (A ∘L S ∘L B) n ≤ ‖A‖ * ‖B‖ * ‖S - F‖ := h1.trans h3
    _ ≤ ‖A‖ * ‖B‖ * (approxNumber S n + ε / (‖A‖ * ‖B‖ + 1)) := by gcongr
    _ = ‖A‖ * ‖B‖ * approxNumber S n + ε * (‖A‖ * ‖B‖ / (‖A‖ * ‖B‖ + 1)) := by ring
    _ ≤ ‖A‖ * ‖B‖ * approxNumber S n + ε * 1 := by
        gcongr
        exact (div_le_one hc).mpr (by linarith)
    _ = ‖A‖ * ‖B‖ * approxNumber S n + ε := by ring

variable {V : H →L[ℂ] K} (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ H)
include hV

theorem adjoint_apply_isometry (x : H) : adjoint V (V x) = x := by
  rw [← comp_apply, hV, id_apply]

theorem norm_isometry_le : ‖V‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  have hx : ⟪V x, V x⟫_ℂ = ⟪x, x⟫_ℂ := by rw [← adjoint_inner_right, adjoint_apply_isometry hV]
  rw [one_mul, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) x, hx]

/-- Isometric transport `T ↦ V T V*` preserves every approximation number. -/
theorem approxNumber_isometric_conj (T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (V ∘L T ∘L adjoint V) n = approxNumber T n := by
  have hnorm := norm_isometry_le hV
  have hnorm' : ‖adjoint V‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hnorm
  have hT : T = adjoint V ∘L (V ∘L T ∘L adjoint V) ∘L V := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [comp_apply]
    rw [adjoint_apply_isometry hV, adjoint_apply_isometry hV]
  refine le_antisymm ?_ ?_
  · calc approxNumber (V ∘L T ∘L adjoint V) n ≤ ‖V‖ * ‖adjoint V‖ * approxNumber T n :=
          approxNumber_sandwich_le V T (adjoint V) n
      _ ≤ 1 * 1 * approxNumber T n := by
          gcongr
          exact approxNumber_nonneg T n
      _ = approxNumber T n := by ring
  · calc approxNumber T n = approxNumber (adjoint V ∘L (V ∘L T ∘L adjoint V) ∘L V) n :=
          congrArg (fun S => approxNumber S n) hT
      _ ≤ ‖adjoint V‖ * ‖V‖ * approxNumber (V ∘L T ∘L adjoint V) n :=
          approxNumber_sandwich_le _ _ _ n
      _ ≤ 1 * 1 * approxNumber (V ∘L T ∘L adjoint V) n := by
          gcongr
          exact approxNumber_nonneg _ n
      _ = approxNumber (V ∘L T ∘L adjoint V) n := by ring

theorem hasSchattenLogResidue_isometric_conj_iff (p : ℝ) (T : H →L[ℂ] H) (R : ℝ) :
    HasSchattenLogResidue p (V ∘L T ∘L adjoint V) R ↔ HasSchattenLogResidue p T R := by
  simp only [HasSchattenLogResidue, schattenPowerPartialSum, approxNumber_isometric_conj hV]

theorem memWeakSchattenClass_isometric_conj_iff (p : ℝ) (T : H →L[ℂ] H) :
    MemWeakSchattenClass p (V ∘L T ∘L adjoint V) ↔ MemWeakSchattenClass p T := by
  simp only [MemWeakSchattenClass, approxNumber_isometric_conj hV]

end IsometricTransport

/-! ## The prime-formed carrier and the integral finite-part translation -/

theorem adjoint_gradeEmbedding_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : ℕ → E) (hu : ∀ n, ‖u n‖ = 1) :
    adjoint (gradeEmbedding u hu) ∘L gradeEmbedding u hu = ContinuousLinearMap.id ℂ _ := by
  ext c n
  rw [comp_apply, adjoint_gradeEmbedding_apply, gradeEmbedding_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu, id_apply]
  simp

/-- The prime-formed orthonormal family `u_j = V e_j`. -/
def formedBasis (j : ℕ) : HistoryL2 (Lp ℂ 2 expPairLaw) := formationEmbedding (historyCoord j)

/-- **(PHSR.15).**  `𝒟_N = V D_N V*`. -/
def formedElapsedDefect (N : ℕ) :
    HistoryL2 (Lp ℂ 2 expPairLaw) →L[ℂ] HistoryL2 (Lp ℂ 2 expPairLaw) :=
  formationEmbedding ∘L elapsedHistoryDefect N ∘L adjoint formationEmbedding

theorem formation_cancel (c : HistoryScalar) :
    adjoint formationEmbedding (formationEmbedding c) = c :=
  adjoint_apply_isometry (adjoint_gradeEmbedding_comp _ _) c

theorem inner_formedBasis (i k : ℕ) :
    ⟪formedBasis i, formedBasis k⟫_ℂ = if i = k then 1 else 0 := by
  rw [formedBasis, formedBasis, ← adjoint_inner_right, formation_cancel, inner_historyCoord]

/-- **(PHSR.15).**  `𝒟_N u_j = d_{N,j} u_j`. -/
theorem formedElapsedDefect_formedBasis (N j : ℕ) :
    formedElapsedDefect N (formedBasis j) = ((elapsedDefect N j : ℝ) : ℂ) • formedBasis j := by
  rw [formedElapsedDefect, comp_apply, comp_apply, formedBasis, formation_cancel,
    elapsedHistoryDefect_basis, map_smul]

/-- **(PHSR.16).**  `𝖳 u_j = w_j u_j`. -/
theorem hodgeCollisionRecord_formedBasis (j : ℕ) :
    hodgeCollisionRecord (formedBasis j) = (PrimeHodgeHistory.w j : ℂ) • formedBasis j := by
  rw [← hodgeCollisionRecord_eq_formation_conj, comp_apply, comp_apply, formedBasis,
    formation_cancel, steinIncidence_basis, map_smul]

/-- **(PHSR.15).**  `𝒟_N` has the singular values of `D_N`. -/
theorem approxNumber_formedElapsedDefect (N n : ℕ) :
    approxNumber (formedElapsedDefect N) n = elapsedDefect N n := by
  rw [formedElapsedDefect, approxNumber_isometric_conj (adjoint_gradeEmbedding_comp _ _),
    approxNumber_elapsedHistoryDefect]

theorem formedElapsedDefect_add_smul_eq (N : ℕ) (z : ℂ) :
    formationEmbedding ∘L (elapsedHistoryDefect N + z • steinIncidence) ∘L
        adjoint formationEmbedding
      = formedElapsedDefect N + z • (formationEmbedding ∘L steinIncidence ∘L
          adjoint formationEmbedding) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [formedElapsedDefect, add_apply, smul_apply, comp_apply, map_add, map_smul]

theorem formedElapsedDefect_add_smul_conj (N : ℕ) (z : ℂ) :
    formedElapsedDefect N + z • hodgeCollisionRecord
      = formationEmbedding ∘L (elapsedHistoryDefect N + z • steinIncidence) ∘L
        adjoint formationEmbedding := by
  rw [formedElapsedDefect_add_smul_eq, hodgeCollisionRecord_eq_formation_conj]

theorem memSchattenClass_one_smul_steinIncidence (z : ℂ) :
    MemSchattenClass 1 (z • steinIncidence) := by
  have hΦ : MemSchattenClass 1 steinIncidence := steinIncidence_nuclear.2.1
  unfold MemSchattenClass at hΦ ⊢
  simp_rw [approxNumber_smul, Real.rpow_one] at hΦ ⊢
  exact hΦ.mul_left _

/-- **Theorem PHSR-E, (PHSR.17).**  `Res(𝒟_N + z𝖳) = 3N` for every `z`. -/
theorem hasSchattenLogResidue_formed_add_smul (N : ℕ) (z : ℂ) :
    HasSchattenLogResidue 1 (formedElapsedDefect N + z • hodgeCollisionRecord) (3 * N) := by
  rw [formedElapsedDefect_add_smul_conj,
    hasSchattenLogResidue_isometric_conj_iff (adjoint_gradeEmbedding_comp _ _),
    hasSchattenLogResidue_one_add_iff_of_memSchattenClass_one
      (isCompactOperator_elapsedHistoryDefect N) (memSchattenClass_one_smul_steinIncidence z)]
  exact hasSchattenLogResidue_elapsedHistoryDefect N

theorem inner_formed_add_smul_basis (N : ℕ) (z : ℂ) (k : ℕ) :
    ⟪formedBasis k, (formedElapsedDefect N + z • hodgeCollisionRecord) (formedBasis k)⟫_ℂ
      = ((elapsedDefect N k : ℝ) : ℂ) + z * (PrimeHodgeHistory.w k : ℂ) := by
  rw [add_apply, smul_apply, formedElapsedDefect_formedBasis, hodgeCollisionRecord_formedBasis,
    inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right, inner_formedBasis,
    if_pos rfl]
  ring

/-- **Theorem PHSR-E, (PHSR.17).**  `FP(𝒟_N + z𝖳) = FP(D_N) + z` in the prime-formed basis. -/
theorem tendsto_formed_add_smul_sub_log (N : ℕ) (z : ℂ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, ⟪formedBasis k,
        (formedElapsedDefect N + z • hodgeCollisionRecord) (formedBasis k)⟫_ℂ
        - 3 * N * (Real.log K : ℂ)) atTop (𝓝 (elapsedFinitePart N + z)) := by
  simp_rw [inner_formed_add_smul_basis]
  have hw : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, (PrimeHodgeHistory.w k : ℂ)) atTop
      (𝓝 1) := by
    simpa using (Complex.hasSum_ofReal.mpr PrimeHodgeHistory.hasSum_w).tendsto_sum_nat
  have h := (tendsto_sum_elapsedDefect_sub_log N).add (hw.const_mul z)
  rw [mul_one] at h
  refine h.congr fun K => ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  ring

/-! ## The theta clock -/

section ThetaClock

variable (a : ℝ)

/-- The theta survival ratio `ρ_n = q_{n+1}/q_n`. -/
def thetaSurvivalRatio (n : ℕ) : ℝ := thetaSurvivalMoment a (n + 1) / thetaSurvivalMoment a n

/-- **(PHSR.18).**  The theta hazard `h_n = 1 - ρ_n`. -/
def thetaHazard (n : ℕ) : ℝ := 1 - thetaSurvivalRatio a n

theorem integrable_tanh_sq_pow (n : ℕ) :
    Integrable (fun x => (Real.tanh (a * x) ^ 2) ^ n) (thetaBalanceLaw a) :=
  (integrable_const 1).mono'
    (((measurable_tanh_mul a).pow_const 2).pow_const n).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact tanh_sq_pow_le_one _ n)

theorem thetaSurvivalMoment_zero : thetaSurvivalMoment a 0 = 1 := by
  simp [thetaSurvivalMoment]

theorem thetaSurvivalMoment_succ_le (n : ℕ) :
    thetaSurvivalMoment a (n + 1) ≤ thetaSurvivalMoment a n :=
  integral_mono (integrable_tanh_sq_pow a _) (integrable_tanh_sq_pow a _) fun x => by
    have h0 : 0 ≤ Real.tanh (a * x) ^ 2 := sq_nonneg _
    have h1 : Real.tanh (a * x) ^ 2 ≤ 1 := by simpa using tanh_sq_pow_le_one (a * x) 1
    rw [pow_succ (Real.tanh (a * x) ^ 2) n]
    exact mul_le_of_le_one_right (pow_nonneg h0 n) h1

theorem thetaBalanceDensity_pos (x : ℝ) : 0 < thetaBalanceDensity a x :=
  div_pos (mul_pos (Real.cosh_pos _) (thetaCuspFullSource_pos_all x)) (thetaBalanceMass_pos a)

/-- The balanced theta law charges every set of positive Lebesgue measure. -/
theorem thetaBalanceLaw_ne_zero {s : Set ℝ} (hs : volume s ≠ 0) : thetaBalanceLaw a s ≠ 0 := by
  rw [thetaBalanceLaw, Ne, withDensity_apply_eq_zero'
    (measurable_thetaBalanceDensity a).ennreal_ofReal.aemeasurable]
  have hset : {x : ℝ | ENNReal.ofReal (thetaBalanceDensity a x) ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun x => by
      simpa using thetaBalanceDensity_pos a x
  rw [hset, Set.univ_inter]
  exact hs

theorem tanh_mul_ne_zero {a : ℝ} (ha : a ≠ 0) {x : ℝ} (hx : x ≠ 0) : Real.tanh (a * x) ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_ne_zero (Real.sinh_eq_zero.not.mpr (mul_ne_zero ha hx)) (Real.cosh_pos _).ne'

/-- **Theorem PHSR-F.**  All theta survival moments are positive. -/
theorem thetaSurvivalMoment_pos {a : ℝ} (ha : a ≠ 0) (n : ℕ) : 0 < thetaSurvivalMoment a n := by
  rw [thetaSurvivalMoment, integral_pos_iff_support_of_nonneg (fun x => by positivity)
    (integrable_tanh_sq_pow a n)]
  refine pos_iff_ne_zero.mpr (thetaBalanceLaw_ne_zero a fun h => ?_)
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support fun x => (Real.tanh (a * x) ^ 2) ^ n :=
    fun x hx => pow_ne_zero n (pow_ne_zero 2 (tanh_mul_ne_zero ha (ne_of_gt hx)))
  have h0 := measure_mono_null hsub h
  rw [Real.volume_Ioi] at h0
  exact ENNReal.top_ne_zero h0

theorem thetaSurvivalRatio_nonneg (n : ℕ) : 0 ≤ thetaSurvivalRatio a n :=
  div_nonneg (thetaSurvivalMoment_nonneg a _) (thetaSurvivalMoment_nonneg a _)

theorem thetaSurvivalRatio_le_one (n : ℕ) : thetaSurvivalRatio a n ≤ 1 :=
  div_le_one_of_le₀ (thetaSurvivalMoment_succ_le a n) (thetaSurvivalMoment_nonneg a n)

/-- Cauchy–Schwarz log-convexity `q_{n+1}² ≤ q_n q_{n+2}`. -/
theorem thetaSurvivalMoment_sq_le (n : ℕ) :
    thetaSurvivalMoment a (n + 1) ^ 2
      ≤ thetaSurvivalMoment a n * thetaSurvivalMoment a (n + 1 + 1) := by
  rw [← norm_thetaSurvival_pow_sq a (n + 1), ← norm_thetaSurvival_pow_sq a n,
    ← norm_thetaSurvival_pow_sq a (n + 1 + 1)]
  set ψ := thetaState a
  set S := thetaSurvival a
  have hS : adjoint S = S := adjoint_contractionMul _ _ _
  have e1 : (S ^ (n + 1)) ψ = S ((S ^ n) ψ) := by
    rw [pow_succ', mul_apply_eq_comp]
  have e2 : (S ^ (n + 1 + 1)) ψ = S ((S ^ (n + 1)) ψ) := by
    rw [pow_succ' S (n + 1), mul_apply_eq_comp]
  have h1 : ⟪(S ^ (n + 1)) ψ, (S ^ (n + 1)) ψ⟫_ℂ = ⟪(S ^ n) ψ, (S ^ (n + 1 + 1)) ψ⟫_ℂ :=
    calc ⟪(S ^ (n + 1)) ψ, (S ^ (n + 1)) ψ⟫_ℂ = ⟪S ((S ^ n) ψ), (S ^ (n + 1)) ψ⟫_ℂ := by
          rw [e1]
      _ = ⟪(S ^ n) ψ, adjoint S ((S ^ (n + 1)) ψ)⟫_ℂ := (adjoint_inner_right S _ _).symm
      _ = ⟪(S ^ n) ψ, (S ^ (n + 1 + 1)) ψ⟫_ℂ := by rw [hS, e2]
  have h2 : ‖(S ^ (n + 1)) ψ‖ ^ 2 ≤ ‖(S ^ n) ψ‖ * ‖(S ^ (n + 1 + 1)) ψ‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) ((S ^ n) ψ) ((S ^ (n + 1 + 1)) ψ)
    rw [← h1, inner_self_eq_norm_sq_to_K] at h
    simpa [norm_pow] using h
  calc (‖(S ^ (n + 1)) ψ‖ ^ 2) ^ 2 ≤ (‖(S ^ n) ψ‖ * ‖(S ^ (n + 1 + 1)) ψ‖) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = ‖(S ^ n) ψ‖ ^ 2 * ‖(S ^ (n + 1 + 1)) ψ‖ ^ 2 := by ring

variable {a}

theorem thetaSurvivalRatio_le_succ (ha : a ≠ 0) (n : ℕ) :
    thetaSurvivalRatio a n ≤ thetaSurvivalRatio a (n + 1) := by
  unfold thetaSurvivalRatio
  rw [div_le_div_iff₀ (thetaSurvivalMoment_pos ha n) (thetaSurvivalMoment_pos ha (n + 1))]
  nlinarith [thetaSurvivalMoment_sq_le a n]

/-- **Theorem PHSR-F.**  `ρ_n` increases. -/
theorem thetaSurvivalRatio_monotone (ha : a ≠ 0) : Monotone (thetaSurvivalRatio a) :=
  monotone_nat_of_le_succ (thetaSurvivalRatio_le_succ ha)

theorem thetaSurvivalRatio_zero_pos (ha : a ≠ 0) : 0 < thetaSurvivalRatio a 0 :=
  div_pos (thetaSurvivalMoment_pos ha 1) (thetaSurvivalMoment_pos ha 0)

theorem thetaSurvivalMoment_succ_eq (ha : a ≠ 0) (n : ℕ) :
    thetaSurvivalMoment a (n + 1) = thetaSurvivalRatio a n * thetaSurvivalMoment a n := by
  rw [thetaSurvivalRatio, div_mul_cancel₀ _ (thetaSurvivalMoment_pos ha n).ne']

/-- The theta law has mass arbitrarily far out: `tanh(ax)²` exceeds every `L < 1` on a half-line. -/
theorem exists_tanh_sq_gt (ha : a ≠ 0) {L : ℝ} (hL : L < 1) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ x, t₀ < x → L < Real.tanh (a * x) ^ 2 := by
  have hlim : Tendsto (fun y => Real.tanh y ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_tanh_atTop_one.pow 2
  obtain ⟨y, hy, hy0⟩ := ((hlim.eventually_const_lt hL).and (eventually_gt_atTop 0)).exists
  have ha' : 0 < |a| := abs_pos.mpr ha
  refine ⟨y / |a|, div_pos hy0 ha', fun x hx => ?_⟩
  have hx0 : 0 < x := (div_pos hy0 ha').trans hx
  have hmono : Real.tanh y ≤ Real.tanh (|a * x|) := by
    refine _root_.HTGeometry.tanh_strictMono.monotone ?_
    rw [abs_mul, abs_of_pos hx0]
    have := (div_lt_iff₀ ha').mp hx
    linarith
  have hty : 0 ≤ Real.tanh y := by
    have := _root_.HTGeometry.tanh_strictMono.monotone hy0.le
    rwa [Real.tanh_zero] at this
  calc L < Real.tanh y ^ 2 := hy
    _ ≤ Real.tanh (|a * x|) ^ 2 := pow_le_pow_left₀ hty hmono 2
    _ = Real.tanh (a * x) ^ 2 := by rw [← abs_tanh_eq, sq_abs]

/-- **Theorem PHSR-F.**  `ρ_n → 1`. -/
theorem tendsto_thetaSurvivalRatio (ha : a ≠ 0) :
    Tendsto (thetaSurvivalRatio a) atTop (𝓝 1) := by
  have hbdd : BddAbove (Set.range (thetaSurvivalRatio a)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact thetaSurvivalRatio_le_one a n⟩
  have hlim := tendsto_atTop_ciSup (thetaSurvivalRatio_monotone ha) hbdd
  set L := ⨆ n, thetaSurvivalRatio a n
  have hL1 : L ≤ 1 := ciSup_le (thetaSurvivalRatio_le_one a)
  suffices hL : L = 1 by rwa [hL] at hlim
  by_contra hne
  have hlt : L < 1 := lt_of_le_of_ne hL1 hne
  have hle : ∀ n, thetaSurvivalRatio a n ≤ L := fun n => le_ciSup hbdd n
  have hL0 : 0 ≤ L := (thetaSurvivalRatio_nonneg a 0).trans (hle 0)
  have hq : ∀ N : ℕ, thetaSurvivalMoment a N ≤ L ^ N := by
    intro N
    induction N with
    | zero => rw [thetaSurvivalMoment_zero, pow_zero]
    | succ k ih =>
      rw [thetaSurvivalMoment_succ_eq ha, pow_succ]
      calc thetaSurvivalRatio a k * thetaSurvivalMoment a k ≤ L * thetaSurvivalMoment a k :=
            mul_le_mul_of_nonneg_right (hle k) (thetaSurvivalMoment_nonneg a k)
        _ ≤ L * L ^ k := mul_le_mul_of_nonneg_left ih hL0
        _ = L ^ k * L := mul_comm _ _
  set L' := (1 + L) / 2 with hL'def
  have hLL' : L < L' := by linarith
  have hL'0 : 0 < L' := by linarith
  obtain ⟨t₀, -, ht₀⟩ := exists_tanh_sq_gt ha (show L' < 1 by linarith)
  have hc : 0 < (thetaBalanceLaw a).real (Set.Ioi t₀) := by
    rw [measureReal_def]
    refine ENNReal.toReal_pos (thetaBalanceLaw_ne_zero a ?_) (measure_ne_top _ _)
    rw [Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  have hlow : ∀ N : ℕ, L' ^ N * (thetaBalanceLaw a).real (Set.Ioi t₀)
      ≤ thetaSurvivalMoment a N := by
    intro N
    have hind : ∫ x, (Set.Ioi t₀).indicator (fun _ => L' ^ N) x ∂thetaBalanceLaw a
        = L' ^ N * (thetaBalanceLaw a).real (Set.Ioi t₀) := by
      rw [integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_comm]
    rw [← hind]
    refine integral_mono ((integrable_const _).indicator measurableSet_Ioi)
      (integrable_tanh_sq_pow a N) fun x => ?_
    by_cases hx : x ∈ Set.Ioi t₀
    · rw [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ hL'0.le (ht₀ x hx).le N
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hratio : Tendsto (fun N : ℕ => (L / L') ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hL0 hL'0.le) ((div_lt_one hL'0).mpr hLL')
  have hbound : ∀ N : ℕ, (thetaBalanceLaw a).real (Set.Ioi t₀) ≤ (L / L') ^ N := fun N => by
    have h1 := (hlow N).trans (hq N)
    rw [div_pow, le_div_iff₀ (pow_pos hL'0 N)]
    linarith
  have := ge_of_tendsto hratio (Eventually.of_forall hbound)
  linarith

theorem thetaHazard_nonneg (n : ℕ) : 0 ≤ thetaHazard a n :=
  sub_nonneg.mpr (thetaSurvivalRatio_le_one a n)

theorem thetaHazard_le_one (n : ℕ) : thetaHazard a n ≤ 1 := by
  have := thetaSurvivalRatio_nonneg a n
  unfold thetaHazard
  linarith

/-- **Theorem PHSR-F.**  `h_n` decreases. -/
theorem thetaHazard_antitone (ha : a ≠ 0) : Antitone (thetaHazard a) := fun m n hmn => by
  have := thetaSurvivalRatio_monotone ha hmn
  unfold thetaHazard
  linarith

/-- **Theorem PHSR-F.**  `h_n → 0`. -/
theorem tendsto_thetaHazard (ha : a ≠ 0) : Tendsto (thetaHazard a) atTop (𝓝 0) := by
  have h := (tendsto_thetaSurvivalRatio ha).const_sub 1
  rw [sub_self] at h
  exact h

/-- **(PHSR.20).**  `-log q_N ≤ ρ_0⁻¹ ∑_{n<N} h_n`. -/
theorem neg_log_thetaSurvivalMoment_le (ha : a ≠ 0) (N : ℕ) :
    -Real.log (thetaSurvivalMoment a N)
      ≤ (thetaSurvivalRatio a 0)⁻¹ * ∑ n ∈ Finset.range N, thetaHazard a n := by
  have hρ0 := thetaSurvivalRatio_zero_pos ha
  induction N with
  | zero => simp [thetaSurvivalMoment_zero]
  | succ k ih =>
    have hρ : 0 < thetaSurvivalRatio a k :=
      hρ0.trans_le (thetaSurvivalRatio_monotone ha (Nat.zero_le k))
    have hlog : -Real.log (thetaSurvivalRatio a k)
        ≤ (thetaSurvivalRatio a 0)⁻¹ * thetaHazard a k := by
      have h1 := Real.one_sub_inv_le_log_of_pos hρ
      have h2 : (thetaSurvivalRatio a k)⁻¹ - 1 = thetaHazard a k / thetaSurvivalRatio a k := by
        unfold thetaHazard
        field_simp
      have h3 : thetaHazard a k / thetaSurvivalRatio a k
          ≤ (thetaSurvivalRatio a 0)⁻¹ * thetaHazard a k := by
        rw [inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (thetaHazard_nonneg k) hρ0
          (thetaSurvivalRatio_monotone ha (Nat.zero_le k))
      linarith
    rw [thetaSurvivalMoment_succ_eq ha, Real.log_mul hρ.ne' (thetaSurvivalMoment_pos ha k).ne',
      Finset.sum_range_succ, mul_add]
    linarith

/-- **Theorem PHSR-F, (PHSR.19).**  `(1/log N) ∑_{n<N} h_n → ∞`. -/
theorem tendsto_sum_thetaHazard_div_log (ha : a ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, thetaHazard a n) / Real.log N) atTop atTop := by
  have hρ0 := thetaSurvivalRatio_zero_pos ha
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨K, hK⟩ := exists_nat_ge (b / thetaSurvivalRatio a 0)
  have hdec := (tendsto_pow_mul_thetaSurvivalMoment a K).eventually_lt_const one_pos
  have hlog1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hdec, hlog1, eventually_ge_atTop 1] with N hN hlogN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hq := thetaSurvivalMoment_pos ha N
  have hlt : (K : ℝ) * Real.log N < -Real.log (thetaSurvivalMoment a N) := by
    have h := Real.log_lt_log (by positivity) hN
    rw [Real.log_one, Real.log_mul (by positivity) hq.ne', Real.log_pow] at h
    linarith
  have hsum := neg_log_thetaSurvivalMoment_le ha N
  have hS : thetaSurvivalRatio a 0 * ((K : ℝ) * Real.log N)
      ≤ ∑ n ∈ Finset.range N, thetaHazard a n := by
    have h1 : thetaSurvivalRatio a 0 * (-Real.log (thetaSurvivalMoment a N))
        ≤ ∑ n ∈ Finset.range N, thetaHazard a n := by
      rw [inv_mul_eq_div, le_div_iff₀ hρ0] at hsum
      linarith
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  have hbK : b ≤ thetaSurvivalRatio a 0 * K := by
    rwa [div_le_iff₀ hρ0, mul_comm] at hK
  nlinarith

theorem norm_thetaHazard_le (n : ℕ) : ‖((thetaHazard a n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (thetaHazard_nonneg n)]
  exact thetaHazard_le_one n

variable (a) in
/-- **(PHSR.18).**  The theta hazard operator `H_a^θ = diag(h_n)`. -/
def thetaHazardOperator : HistoryLine →L[ℂ] HistoryLine :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => ((thetaHazard a n : ℝ) : ℂ)) norm_thetaHazard_le

theorem thetaHazardOperator_basis (n : ℕ) :
    thetaHazardOperator a (historyCoord n) = ((thetaHazard a n : ℝ) : ℂ) • historyCoord n :=
  diagonal_historyCoord _ _ n

/-- **Theorem PHSR-F.**  `H_a^θ ≥ 0`. -/
theorem thetaHazardOperator_isPositive : (thetaHazardOperator a).IsPositive :=
  isPositive_ellTwoDiagonal_ofReal _ _ thetaHazard_nonneg

/-- **Theorem PHSR-F.**  `H_a^θ` is compact. -/
theorem isCompactOperator_thetaHazardOperator (ha : a ≠ 0) :
    IsCompactOperator (thetaHazardOperator a) := by
  refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
    (c := fun n => ((thetaHazard a n : ℝ) : ℂ)) thetaHazardOperator_basis ?_
  rw [Nat.cofinite_eq_atTop]
  simpa [Real.norm_eq_abs, abs_of_nonneg (thetaHazard_nonneg _)] using
    (tendsto_thetaHazard ha).norm

theorem approxNumber_thetaHazardOperator (ha : a ≠ 0) (n : ℕ) :
    approxNumber (thetaHazardOperator a) n = thetaHazard a n :=
  _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq (Equiv.refl ℕ)
    (lam := fun k => ((thetaHazard a k : ℝ) : ℂ)) (r := thetaHazard a)
    (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (thetaHazard_nonneg i)]
      rfl)
    thetaHazard_nonneg (fun h => thetaHazard_antitone ha h) n

/-- **Theorem PHSR-F.**  `H_a^θ` is not weak trace class. -/
theorem not_memWeakSchattenClass_thetaHazardOperator (ha : a ≠ 0) :
    ¬MemWeakSchattenClass 1 (thetaHazardOperator a) := by
  rintro ⟨C, hC, hbound⟩
  have hle : ∀ n : ℕ, thetaHazard a n ≤ C / ((n : ℝ) + 1) := fun n => by
    have h := hbound n
    rwa [Real.rpow_one, approxNumber_thetaHazardOperator ha] at h
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, thetaHazard a n ≤ C * (1 + Real.log N) := by
    intro N
    calc ∑ n ∈ Finset.range N, thetaHazard a n ≤ ∑ n ∈ Finset.range N, C / ((n : ℝ) + 1) :=
          Finset.sum_le_sum fun n _ => hle n
      _ = C * ((harmonic N : ℚ) : ℝ) := by
          rw [harmonic, Rat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          push_cast
          ring
      _ ≤ C * (1 + Real.log N) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hC
  have hev := (tendsto_sum_thetaHazard_div_log ha).eventually_gt_atTop (2 * C + 1)
  have hlog1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N, hN, hlogN⟩ := (hev.and hlog1).exists
  rw [lt_div_iff₀ (by linarith)] at hN
  have hS := hsum N
  have hCL : C * 1 ≤ C * Real.log N := mul_le_mul_of_nonneg_left hlogN hC
  nlinarith

/-- **Theorem PHSR-F.**  No trace-class perturbation identifies the theta hazard with the source
hazard `D_1`. -/
theorem not_traceClass_elapsedHistoryDefect_one_sub_thetaHazard (ha : a ≠ 0) :
    ¬MemSchattenClass 1 (elapsedHistoryDefect 1 - thetaHazardOperator a) := fun h =>
  not_memWeakSchattenClass_thetaHazardOperator ha
    ((memWeakSchattenClass_one_iff_of_memSchattenClass_one_sub h).1
      (memWeakSchattenClass_elapsedHistoryDefect 1))

end ThetaClock

/-- **ULF-PHSR-001.**  The elapsed-history defects `D_N = I - C*ᴺ Cᴺ` are positive compact
diagonals `d_{N,k}` of weak trace class with honest logarithmic residue `3N`, outside `S_1` and
inside every `S_p`, `p > 1`; they satisfy the cocycle `D_{N+M} = D_N + C*ᴺ D_M Cᴺ`, whose exit
currents `E_j = D_{j+1} - D_j` all have residue `3` and pairwise trace-class differences; the
canonical finite part is `FP(D_N) = -(A_N ψ(N+3/2) + B_N ψ(N+5/2) + C_N ψ(N+7/2))/2`, with
`FP(D_1) = -3ψ(9/2)` and `FP(E_j) - FP(E_l) = Tr(E_j - E_l)`; the marked exit record is
`⟨e_0, E_j e_0⟩ = w_j = Tr(P_j 𝖳)` with total `1`; on the prime-formed carrier every integral
multiple of `𝖳` translates the finite part by that integer without moving the residue; and for
every nonzero theta tilt the theta hazard `diag(1 - q_{n+1}/q_n)` is positive compact but not
weak trace class, so it differs from `D_1` by no trace-class operator. -/
theorem prime_hodge_singular_residue_clock :
    (∀ N : ℕ, (elapsedHistoryDefect N).IsPositive ∧ IsCompactOperator (elapsedHistoryDefect N) ∧
      (∀ n, approxNumber (elapsedHistoryDefect N) n = elapsedDefect N n) ∧
      MemWeakSchattenClass 1 (elapsedHistoryDefect N) ∧
      HasSchattenLogResidue 1 (elapsedHistoryDefect N) (3 * N) ∧
      Tendsto (fun k : ℕ => (k : ℝ) * elapsedDefect N k) atTop (𝓝 (3 * N))) ∧
    (∀ N : ℕ, 1 ≤ N → ¬MemSchattenClass 1 (elapsedHistoryDefect N) ∧
      ∀ p : ℝ, 1 < p → MemSchattenClass p (elapsedHistoryDefect N)) ∧
    (∀ N M : ℕ, elapsedHistoryDefect (N + M) = elapsedHistoryDefect N +
      adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L elapsedHistoryDefect M ∘L
        primeHodgeHistorySurvivalShift ^ N) ∧
    (∀ j : ℕ, exitCurrent j = elapsedHistoryDefect (j + 1) - elapsedHistoryDefect j ∧
      MemWeakSchattenClass 1 (exitCurrent j) ∧ HasSchattenLogResidue 1 (exitCurrent j) 3 ∧
      Tendsto (fun k : ℕ => (k : ℝ) * PrimeHodgeHistory.conditionalExitWeight j k) atTop
        (𝓝 3)) ∧
    (∀ N : ℕ, elapsedHistoryDefect N = ∑ j ∈ Finset.range N, exitCurrent j) ∧
    (∀ j l : ℕ, MemSchattenClass 1 (exitCurrent j - exitCurrent l) ∧
      (elapsedFinitePart (j + 1) - elapsedFinitePart j)
          - (elapsedFinitePart (l + 1) - elapsedFinitePart l)
        = opTrace (exitCurrent j - exitCurrent l)) ∧
    (∀ N : ℕ, Tendsto (fun K : ℕ => ((∑ k ∈ Finset.range K, elapsedDefect N k
      - 3 * N * Real.log K : ℝ) : ℂ)) atTop (𝓝 (elapsedFinitePart N))) ∧
    elapsedFinitePart 1 = -3 * Complex.digamma (9 / 2) ∧
    (∀ j : ℕ, Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K,
      ⟪historyCoord k, exitCurrent j (historyCoord k)⟫_ℂ - 3 * (Real.log K : ℂ)) atTop
        (𝓝 (elapsedFinitePart (j + 1) - elapsedFinitePart j))) ∧
    (∀ j : ℕ, ⟪historyCoord 0, exitCurrent j (historyCoord 0)⟫_ℂ = (PrimeHodgeHistory.w j : ℂ) ∧
      (PrimeHodgeHistory.w j : ℂ) = opTrace (historyGrade j ∘L hodgeCollisionRecord)) ∧
    HasSum (fun j => ⟪historyCoord 0, exitCurrent j (historyCoord 0)⟫_ℂ) 1 ∧
    (∀ i k : ℕ, ⟪formedBasis i, formedBasis k⟫_ℂ = if i = k then 1 else 0) ∧
    (∀ N j : ℕ, formedElapsedDefect N (formedBasis j)
        = ((elapsedDefect N j : ℝ) : ℂ) • formedBasis j ∧
      hodgeCollisionRecord (formedBasis j) = (PrimeHodgeHistory.w j : ℂ) • formedBasis j) ∧
    (∀ (N : ℕ) (z : ℤ),
      HasSchattenLogResidue 1 (formedElapsedDefect N + (z : ℂ) • hodgeCollisionRecord) (3 * N) ∧
      Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, ⟪formedBasis k,
          (formedElapsedDefect N + (z : ℂ) • hodgeCollisionRecord) (formedBasis k)⟫_ℂ
          - 3 * N * (Real.log K : ℂ)) atTop (𝓝 (elapsedFinitePart N + z))) ∧
    (∀ a : ℝ, a ≠ 0 → (∀ n, 0 < thetaSurvivalMoment a n) ∧
      Monotone (thetaSurvivalRatio a) ∧ Tendsto (thetaSurvivalRatio a) atTop (𝓝 1) ∧
      Antitone (thetaHazard a) ∧ Tendsto (thetaHazard a) atTop (𝓝 0) ∧
      (thetaHazardOperator a).IsPositive ∧ IsCompactOperator (thetaHazardOperator a) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, thetaHazard a n) / Real.log N) atTop
        atTop ∧
      ¬MemWeakSchattenClass 1 (thetaHazardOperator a) ∧
      ¬MemSchattenClass 1 (elapsedHistoryDefect 1 - thetaHazardOperator a)) := by
  refine ⟨fun N => ⟨elapsedHistoryDefect_isPositive N, isCompactOperator_elapsedHistoryDefect N,
      approxNumber_elapsedHistoryDefect N, memWeakSchattenClass_elapsedHistoryDefect N,
      hasSchattenLogResidue_elapsedHistoryDefect N, tendsto_mul_elapsedDefect N⟩,
    fun N hN => elapsedHistoryDefect_schatten hN, elapsedHistoryDefect_add,
    fun j => ⟨exitCurrent_eq_sub j, (exitCurrent_residue j).1, (exitCurrent_residue j).2,
      tendsto_mul_conditionalExitWeight j⟩,
    elapsedHistoryDefect_eq_sum,
    fun j l => ⟨exitCurrent_sub_traceClass j l, exitCurrent_finitePart_sub_eq_opTrace j l⟩,
    tendsto_sum_elapsedDefect_sub_log, elapsedFinitePart_one, tendsto_sum_exitCurrent_sub_log,
    fun j => ⟨inner_exitCurrent_initial j,
      (inner_exitCurrent_initial j).symm.trans (inner_exitCurrent_initial_eq_opTrace j)⟩,
    hasSum_inner_exitCurrent_initial, inner_formedBasis,
    fun N j => ⟨formedElapsedDefect_formedBasis N j, hodgeCollisionRecord_formedBasis j⟩,
    fun N z => ⟨hasSchattenLogResidue_formed_add_smul N z, tendsto_formed_add_smul_sub_log N z⟩,
    fun a ha => ⟨thetaSurvivalMoment_pos ha, thetaSurvivalRatio_monotone ha,
      tendsto_thetaSurvivalRatio ha, thetaHazard_antitone ha, tendsto_thetaHazard ha,
      thetaHazardOperator_isPositive, isCompactOperator_thetaHazardOperator ha,
      tendsto_sum_thetaHazard_div_log ha, not_memWeakSchattenClass_thetaHazardOperator ha,
      not_traceClass_elapsedHistoryDefect_one_sub_thetaHazard ha⟩⟩

end GaloisForLFunctions.HTGeometry
