import GaloisForLFunctions.RHTower.MobiusHilbertFormCriterion
import GaloisForLFunctions.RHTower.MobiusMertensFiniteSectionEnergy
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# The Möbius Hilbert form grows subpolynomially exactly under RH

Converse of the Hilbert criterion.  Under RH, Littlewood's bound `M(n) ≪ (n+1)^{1/2+δ}` and Abel
summation give the uniform Laplace bound `|F_N(x)| ≤ K x^{-1/2-δ}` on `(0, 1]`.  Near `0` this is
weaker than the trivial bound `|F_N(x)| ≤ N`.  The geometric mean of the two bounds,
`F_N² ≤ (N²)^a (K² x^{-1-2δ})^{1-a}`, is integrable on `(0, 1]` once `(1+2δ)(1-a) < 1`.  This gives
`∫_0^1 F_N² ≪ N^{2a}`, and on `(1, ∞)` the pencil is at most `2e^{-x}`.  Hence

`Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) = O_ε((N+1)^ε)` for every `ε > 0`  ⟺  RH.

The form is nevertheless unbounded: a bounded form would give finite Möbius--Laplace energy on
the critical line itself, which excludes critical-line zeros, contradicting Hardy.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The uniform Abel--Laplace bound for the finite Möbius pencil under a Mertens power bound. -/
theorem abs_finiteMobiusLaplacePencil_le_of_mertensBound {theta C x : ℝ} (htheta : 0 ≤ theta)
    (hC : 0 ≤ C) (hx : 0 < x) (hx1 : x ≤ 1)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤ C * ((n : ℝ) + 1) ^ theta) (N : ℕ) :
    |finiteMobiusLaplacePencil N x| ≤
      C * (Real.exp (theta ^ 2) + 2 ^ theta * mixedSubpowerAbelConstant theta) *
        (1 / x) ^ theta := by
  have hb0 : mobiusComplexCoefficient 0 = 0 := by simp [mobiusComplexCoefficient]
  have hb : ∀ n : ℕ, ‖partialSumSeq mobiusComplexCoefficient n‖ ≤ C * ((n : ℝ) + 1) ^ theta :=
    fun n => by simpa [partialSumSeq, mobiusMertensPartialSum] using hM n
  have h := norm_finiteLaplaceSection_le_of_partialSumSeq_rpow hb0 htheta hC hx hx1 hb N
  have heq : (∑ j ∈ Finset.range N, mobiusComplexCoefficient (j + 1) *
      ((Real.exp (-((j + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ)) =
      ((finiteMobiusLaplacePencil N x : ℝ) : ℂ) := by
    unfold finiteMobiusLaplacePencil finiteRealLaplacePencil shiftedMobiusRealCoefficient
      mobiusComplexCoefficient
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The trivial bound `|F_N(x)| ≤ N` for `x ≥ 0`. -/
theorem abs_finiteMobiusLaplacePencil_le_card (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |finiteMobiusLaplacePencil N x| ≤ N := by
  unfold finiteMobiusLaplacePencil finiteRealLaplacePencil
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ n ∈ Finset.range N,
      |shiftedMobiusRealCoefficient n * Real.exp (-((n + 1 : ℕ) : ℝ) * x)| ≤ 1 := by
    intro n _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |shiftedMobiusRealCoefficient n| ≤ 1 := by
      unfold shiftedMobiusRealCoefficient
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : Real.exp (-((n + 1 : ℕ) : ℝ) * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith)
    calc |shiftedMobiusRealCoefficient n| * Real.exp (-((n + 1 : ℕ) : ℝ) * x) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp

/-- Geometric-mean interpolation of two upper bounds. -/
theorem le_rpow_mul_rpow_of_le {u A B a : ℝ} (hu : 0 ≤ u) (hA : u ≤ A) (hB : u ≤ B)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : u ≤ A ^ a * B ^ (1 - a) := by
  rcases eq_or_lt_of_le hu with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (Real.rpow_nonneg (le_trans hu hA) _) (Real.rpow_nonneg (le_trans hu hB) _)
  · calc u = u ^ a * u ^ (1 - a) := by
          rw [← Real.rpow_add hpos]
          simp
      _ ≤ A ^ a * B ^ (1 - a) :=
          mul_le_mul (Real.rpow_le_rpow hu hA ha0) (Real.rpow_le_rpow hu hB (by linarith))
            (Real.rpow_nonneg hu _) (Real.rpow_nonneg (le_trans hu hA) _)

/-- The far part of the Hilbert energy is at most `1`. -/
theorem setIntegral_Ioi_one_sq_finiteMobiusLaplacePencil_le (N : ℕ) :
    ∫ x in Ioi 1, finiteMobiusLaplacePencil N x ^ 2 ≤ 1 := by
  have hmaj : IntegrableOn (fun x : ℝ => 4 * Real.exp (-2 * x)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 2)).const_mul 4
  have hint : IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2) (Ioi 1) :=
    (integrableOn_sq_finiteMobiusLaplacePencil N).mono_set (Ioi_subset_Ioi zero_le_one)
  calc ∫ x in Ioi 1, finiteMobiusLaplacePencil N x ^ 2
      ≤ ∫ x in Ioi 1, 4 * Real.exp (-2 * x) := by
        refine setIntegral_mono_on hint hmaj measurableSet_Ioi fun x hx => ?_
        have h := sq_finiteMobiusLaplacePencil_le_of_one_le N (le_of_lt hx)
        have he : Real.exp (-(2 * x)) = Real.exp (-2 * x) := by ring_nf
        rw [he] at h
        exact h
    _ = 4 * (Real.exp (-2 * 1) / 2) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
        ring
    _ ≤ 1 := by
        have h1 : Real.exp (-2 * 1) ≤ 1 / 2 := by
          have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have h3 : Real.exp (-2 * 1) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by norm_num)
          have h4 : Real.exp (-1) ≤ 1 / 2 := by
            rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
            linarith
          exact h3.trans h4
        linarith

/-- **Converse of the Hilbert criterion.**  RH implies subpower growth of the Möbius Hilbert form. -/
theorem riemannHypothesis_implies_mobiusHilbertFormSubpower (hRH : RiemannHypothesis) :
    MobiusHilbertFormSubpower := by
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, ∀ N : ℕ,
      finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ ε := by
    intro ε hε hε1
    set δ : ℝ := ε / 8 with hδ
    have hδ0 : 0 < δ := by positivity
    set θ : ℝ := 1 / 2 + δ with hθ
    have hθ0 : 0 ≤ θ := by positivity
    set a : ℝ := ε / 4 with ha
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by linarith
    obtain ⟨C, hC0, hM⟩ :=
      riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ0
    set K : ℝ := C * (Real.exp (θ ^ 2) + 2 ^ θ * mixedSubpowerAbelConstant θ) with hK
    have hK0 : 0 ≤ K := by
      have := mixedSubpowerAbelConstant_nonneg hθ0
      have : 0 ≤ (2 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) _
      rw [hK]
      positivity
    set s : ℝ := -(2 * θ * (1 - a)) with hs
    have hs1 : -1 < s := by
      rw [hs, hθ, ha, hδ]
      nlinarith
    set G : ℝ := (K ^ 2) ^ (1 - a) with hG
    have hG0 : 0 ≤ G := Real.rpow_nonneg (by positivity) _
    have hs0 : 0 < s + 1 := by linarith
    refine ⟨G / (s + 1) + 1, fun N => ?_⟩
    have hint := integrableOn_sq_finiteMobiusLaplacePencil N
    rw [← integral_sq_finiteMobiusLaplacePencil, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
    set A : ℝ := ((N : ℝ) ^ 2) ^ a with hA
    have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
    have hpt : ∀ x ∈ Ioc (0 : ℝ) 1,
        finiteMobiusLaplacePencil N x ^ 2 ≤ A * G * x ^ s := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hbig := abs_finiteMobiusLaplacePencil_le_of_mertensBound hθ0 hC0 hx0 hx.2 hM N
      rw [← hK] at hbig
      have hsmall := abs_finiteMobiusLaplacePencil_le_card N hx0.le
      have hxθ : (1 / x) ^ θ = x ^ (-θ) := by
        rw [one_div, Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
      rw [hxθ] at hbig
      have hB : finiteMobiusLaplacePencil N x ^ 2 ≤ K ^ 2 * x ^ (-(2 * θ)) := by
        calc finiteMobiusLaplacePencil N x ^ 2 = |finiteMobiusLaplacePencil N x| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (K * x ^ (-θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbig 2
          _ = K ^ 2 * x ^ (-(2 * θ)) := by
              rw [mul_pow, ← Real.rpow_natCast (x ^ (-θ)), ← Real.rpow_mul hx0.le]
              congr 2
              push_cast
              ring
      have hAb : finiteMobiusLaplacePencil N x ^ 2 ≤ (N : ℝ) ^ 2 := by
        calc finiteMobiusLaplacePencil N x ^ 2 = |finiteMobiusLaplacePencil N x| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsmall 2
      have hmix := le_rpow_mul_rpow_of_le (sq_nonneg _) hAb hB ha0 ha1
      calc finiteMobiusLaplacePencil N x ^ 2
          ≤ ((N : ℝ) ^ 2) ^ a * (K ^ 2 * x ^ (-(2 * θ))) ^ (1 - a) := hmix
        _ = A * G * x ^ s := by
            rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx0.le _),
              ← Real.rpow_mul hx0.le, hA, hG, hs]
            ring_nf
    have hmaj : IntegrableOn (fun x : ℝ => A * G * x ^ s) (Ioc 0 1) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hs1).const_mul (A * G)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
    have hnear : ∫ x in Ioc 0 1, finiteMobiusLaplacePencil N x ^ 2 ≤ A * G / (s + 1) := by
      calc ∫ x in Ioc 0 1, finiteMobiusLaplacePencil N x ^ 2
          ≤ ∫ x in Ioc 0 1, A * G * x ^ s :=
            setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) hmaj measurableSet_Ioc hpt
        _ = A * G * ∫ x in Ioc 0 1, x ^ s := integral_const_mul _ _
        _ = A * G / (s + 1) := by
            rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hs1),
              Real.one_rpow, Real.zero_rpow (by linarith)]
            ring
    have hfar := setIntegral_Ioi_one_sq_finiteMobiusLaplacePencil_le N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hpow1 : 1 ≤ ((N : ℝ) + 1) ^ ε := Real.one_le_rpow hN1 hε.le
    have hAN : A ≤ ((N : ℝ) + 1) ^ ε := by
      calc A = ((N : ℝ) ^ 2) ^ a := hA
        _ ≤ (((N : ℝ) + 1) ^ 2) ^ a :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2) ha0
        _ = ((N : ℝ) + 1) ^ (2 * a) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ ((N : ℝ) + 1) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by rw [ha]; linarith)
    have hGs : 0 ≤ G / (s + 1) := div_nonneg hG0 hs0.le
    calc (∫ x in Ioc 0 1, finiteMobiusLaplacePencil N x ^ 2) +
          ∫ x in Ioi 1, finiteMobiusLaplacePencil N x ^ 2
        ≤ A * G / (s + 1) + 1 := add_le_add hnear hfar
      _ = A * (G / (s + 1)) + 1 := by ring
      _ ≤ ((N : ℝ) + 1) ^ ε * (G / (s + 1)) + ((N : ℝ) + 1) ^ ε :=
          add_le_add (mul_le_mul_of_nonneg_right hAN hGs) hpow1
      _ = (G / (s + 1) + 1) * ((N : ℝ) + 1) ^ ε := by ring
  intro ε hε
  rcases le_or_gt ε 1 with h | h
  · exact key ε hε h
  · obtain ⟨C, hC⟩ := key 1 one_pos le_rfl
    refine ⟨max C 0, fun N => ?_⟩
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    calc finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ (1 : ℝ) := hC N
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h.le) (le_max_right _ _)

/-- **Hilbert criterion, closed.**  The Möbius Hilbert form `Σ_{m,n ≤ N} μ(m)μ(n)/(m+n)` grows
subpolynomially if and only if the Riemann hypothesis holds. -/
theorem mobiusHilbertFormSubpower_iff_riemannHypothesis :
    MobiusHilbertFormSubpower ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_mobiusHilbertFormSubpower, riemannHypothesis_implies_mobiusHilbertFormSubpower⟩

/-- **The Möbius Hilbert form is unbounded.**  A uniform bound would put the logarithmic
Möbius--Laplace source in `L²` on `Re s = 1/2`, which excludes every zeta zero on that line;
Hardy's theorem supplies one. -/
theorem not_exists_forall_finiteMobiusGammaHankelEnergy_one_le :
    ¬ ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ B := by
  rintro ⟨B, hB⟩
  have hmem := (memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (sigma := 1 / 2) (B := B) (by norm_num) (by norm_num; exact hB)).1
  obtain ⟨T₀, _, hT₀⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _, hζ⟩ := hT₀ T₀ le_rfl
  refine riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed
    (sigma := 1 / 2) (by norm_num) (by norm_num) hmem (rho := linePt τ) ?_ ?_ hζ
  · simp [linePt]
  · intro h
    have := congrArg Complex.re h
    simp [linePt] at this

end RHTower
