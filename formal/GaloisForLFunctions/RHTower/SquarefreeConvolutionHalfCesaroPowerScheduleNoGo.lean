import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroVanishingNecessity
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel

/-!
# Polynomial Cesàro schedule no-go

Polynomial Abel continuation sharpens the fast-schedule obstruction.  At a real point `sigma`
above `1/2`, raw convolution-half partial sums cannot have polynomial exponent below `1 - sigma`:
such a bound would continue their Dirichlet series across the simple zeta pole at one.

At `sigma = 6/11`, pole amplification comparable to `N^rho` makes one Cesàro discrete derivative
grow with exponent at most `1 - rho`.  Hence every `rho > 6/11` is already impossible.  The
remaining schedules are substantially slower than the earlier fast threshold `rho = 1`.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

/-- Partial sums of the convolution half cannot have polynomial exponent below the distance to
the zeta pole. -/
theorem not_exists_poly_bound_squarefreeHalfDirichletPartialSum
    {sigma alpha : ℝ} (hsigmaHalf : 1 / 2 < sigma)
    (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 - sigma) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤
        C * (N : ℝ) ^ alpha := by
  rintro ⟨C, hC0, hC⟩
  let tau : ℝ := (sigma + alpha + 1) / 2
  have hsigmaAlphaTau : sigma + alpha < tau := by
    dsimp [tau]
    linarith
  have htauOne : tau < 1 := by
    dsimp [tau]
    linarith
  have hshiftBound : ∀ N : ℕ,
      ‖dirichletPartialSum squarefreeConvolutionHalfShift N (sigma : ℂ)‖ ≤
        C * ((N : ℝ) + 1) ^ alpha := by
    intro N
    rw [dirichletPartialSum_squarefreeConvolutionHalfShift]
    have h := hC (N + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hconv : DirichletConvergesAt squarefreeConvolutionHalfShift (tau : ℂ) := by
    have h := tendsto_dirichlet_partialSum_of_poly_bounded hC0 halpha0 hshiftBound
      (s := (tau : ℂ) - (sigma : ℂ)) (by
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith)
    obtain ⟨L, hL⟩ := h
    refine ⟨L, ?_⟩
    convert hL using 1
    ext N
    unfold dirichletPartialSum squarefreeConvolutionHalfShift
    apply Finset.sum_congr rfl
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
    rw [mul_assoc, ← Complex.cpow_add _ _ hne]
    congr 2
    ring
  let F : ℂ → ℂ := dirichletSum squarefreeConvolutionHalfShift
  let U : Set ℂ := {s : ℂ | tau < s.re}
  have hFdiff : DifferentiableOn ℂ F U := by
    simpa [F, U] using differentiableOn_dirichletSum hconv
  have hFana : AnalyticOnNhd ℂ F U :=
    hFdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hFeq : EqOn F (LSeries squarefreeConvolutionHalf) farHalf := by
    intro s hs
    have hstau : tau < s.re := by
      have hsone := mem_farHalf.mp hs
      linarith
    have hconvS : DirichletConvergesAt squarefreeConvolutionHalfShift s :=
      tendsto_dirichlet_partialSum_of_re_lt hconv (by simpa using hstau)
    have hleft := tendsto_dirichletSum hconvS
    have hleft' : Tendsto (fun N => squarefreeHalfDirichletPartialSum (N + 1) s)
        atTop (𝓝 (F s)) := by
      simpa [F, dirichletPartialSum_squarefreeConvolutionHalfShift] using hleft
    have hright0 :=
      tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.tendsto_at hs
    have hright : Tendsto (fun N => squarefreeHalfDirichletPartialSum (N + 1) s)
        atTop (𝓝 (LSeries squarefreeConvolutionHalf s)) :=
      hright0.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hleft' hright
  let H : ℂ → ℂ := fun s =>
    (s - 1) * F s ^ 2 * riemannZeta (2 * s) - zetaResidueUnit s
  have hHana : AnalyticOnNhd ℂ H U := by
    intro s hs
    have htwo : 2 * s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      change tau < s.re at hs
      have hhalfTau : 1 / 2 < tau := by
        dsimp [tau]
        linarith
      linarith
    exact (((show AnalyticAt ℂ (fun z : ℂ => z - 1) s by fun_prop).mul
      ((hFana s hs).pow 2)).mul
      ((analyticOn_riemannZeta (2 * s) htwo).comp (by fun_prop))).sub
      (analyticAt_zetaResidueUnit s)
  have hHzeroFar : EqOn H 0 farHalf := by
    intro s hs
    have hs1 : 1 < s.re := mem_farHalf.mp hs
    have htwo : riemannZeta (2 * s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith)
    have htwo' : riemannZeta (s * 2) ≠ 0 := by simpa [mul_comm] using htwo
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      norm_num at hs1
    dsimp [H]
    rw [hFeq hs, LSeries_squarefreeConvolutionHalf_sq hs1]
    rw [zetaResidueUnit, Function.update_of_ne hsne]
    field_simp [htwo']
    ring
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_re_gt tau).isPreconnected
  have honeU : (1 : ℂ) ∈ U := by
    change tau < (1 : ℂ).re
    simpa using htauOne
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hfar : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf :=
      isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 :=
      hfar.mono (fun s hs => hHzeroFar hs)
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have htwoU : (2 : ℂ) ∈ U := by
    change tau < (2 : ℂ).re
    norm_num
    linarith
  have hzeroAll := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hUpre htwoU hfreq
  have hzero := hzeroAll honeU
  dsimp [H] at hzero
  rw [zetaResidueUnit_one] at hzero
  norm_num at hzero

/-- Eventual form of the sharp polynomial partial-sum obstruction. -/
theorem not_exists_eventual_poly_bound_squarefreeHalfDirichletPartialSum
    {sigma alpha : ℝ} (hsigmaHalf : 1 / 2 < sigma)
    (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 - sigma) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤
        C * (N : ℝ) ^ alpha := by
  rintro ⟨C, hC0, N₀, hC⟩
  apply not_exists_poly_bound_squarefreeHalfDirichletPartialSum
    hsigmaHalf halpha0 halpha
  let H : ℝ := ∑ N ∈ Finset.range N₀,
    ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖
  have hmax0 : 0 ≤ max C H := hC0.trans (le_max_left _ _)
  refine ⟨max C H, hmax0, fun N => ?_⟩
  rcases N with _ | N
  · rw [show squarefreeHalfDirichletPartialSum 0 (sigma : ℂ) = 0 by
      simp [squarefreeHalfDirichletPartialSum], norm_zero]
    simpa only [Nat.cast_zero] using
      mul_nonneg hmax0 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) alpha)
  · have hpow : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ alpha :=
      Real.one_le_rpow (by exact_mod_cast Nat.succ_pos N) halpha0
    by_cases hN : N₀ ≤ N + 1
    · exact (hC (N + 1) hN).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (by positivity : 0 ≤ (((N + 1 : ℕ) : ℝ))) alpha))
    · have hmem : N + 1 ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
      have hterm : ‖squarefreeHalfDirichletPartialSum (N + 1) (sigma : ℂ)‖ ≤ H := by
        dsimp [H]
        exact Finset.single_le_sum (fun i _ => norm_nonneg
          (squarefreeHalfDirichletPartialSum i (sigma : ℂ))) hmem
      calc
        ‖squarefreeHalfDirichletPartialSum (N + 1) (sigma : ℂ)‖ ≤ H := hterm
        _ ≤ max C H := le_max_right _ _
        _ = (max C H) * 1 := by ring
        _ ≤ (max C H) * ((N + 1 : ℕ) : ℝ) ^ alpha :=
          mul_le_mul_of_nonneg_left hpow hmax0

/-- Certified pole amplification dominates a positive power of cutoff. -/
def CesaroPoleSchedulePowerDominating (kappa : ℕ → ℕ) (rho : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    24 ≤ kappa N ∧ (N : ℝ) ^ rho ≤ B * (5 : ℝ) ^ (kappa N - 24)

/-- Power-schedule no-go below fastness: amplification exponent above `6/11` already contradicts
the zeta pole after one Cesàro discrete derivative. -/
theorem no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_powerDominating
    {kappa : ℕ → ℕ} {rho : ℝ} (hrho : 6 / 11 < rho) (hrhoOne : rho ≤ 1)
    (hpower : CesaroPoleSchedulePowerDominating kappa rho) :
    ¬ PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa := by
  rintro hloc
  obtain ⟨B, hB, N₀, hpower⟩ := hpower
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCesaroScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hC0 : 0 ≤ C :=
    (norm_nonneg
      (poleClearedFirstTraceCesaroScheduledApprox kappa 0 boundaryExteriorPoint)).trans (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hBK0 : 0 ≤ B * K := mul_nonneg hB hK0
  have hweighted : ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ^ rho * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ B * K := by
    intro N hN
    obtain ⟨hk24, hscale⟩ := hpower N hN
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow hk24
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hbound N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K := by
      rw [poleClearedFirstTraceCesaroScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hpowprod :
        (5 : ℝ) ^ (kappa N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K :=
      (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hprod
    calc
      (N : ℝ) ^ rho * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          (B * (5 : ℝ) ^ (kappa N - 24)) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
      _ = B * ((5 : ℝ) ^ (kappa N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖) := by ring
      _ ≤ B * K := mul_le_mul_of_nonneg_left hpowprod hB
  let beta : ℝ := 1 - rho
  have hbeta0 : 0 ≤ beta := by dsimp [beta]; linarith
  have hbetaLt : beta < 1 - (6 / 11 : ℝ) := by dsimp [beta]; linarith
  have hscaled : ∀ m : ℕ, N₀ ≤ m → 1 ≤ m →
      (m : ℝ) * ‖squarefreeHalfCesaroSum m boundaryExteriorPoint‖ ≤
        (B * K) * (m : ℝ) ^ beta := by
    intro m hmN hm1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
    have hpowEq : (m : ℝ) = (m : ℝ) ^ rho * (m : ℝ) ^ beta := by
      calc
        (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ = (m : ℝ) ^ (rho + beta) := by congr 1; dsimp [beta]; ring
        _ = (m : ℝ) ^ rho * (m : ℝ) ^ beta := Real.rpow_add hmpos _ _
    calc
      (m : ℝ) * ‖squarefreeHalfCesaroSum m boundaryExteriorPoint‖ =
          ((m : ℝ) ^ rho * (m : ℝ) ^ beta) *
            ‖squarefreeHalfCesaroSum m boundaryExteriorPoint‖ :=
        congrArg (fun x : ℝ => x *
          ‖squarefreeHalfCesaroSum m boundaryExteriorPoint‖) hpowEq
      _ = (m : ℝ) ^ beta *
            ((m : ℝ) ^ rho * ‖squarefreeHalfCesaroSum m boundaryExteriorPoint‖) := by ring
      _ ≤ (m : ℝ) ^ beta * (B * K) :=
        mul_le_mul_of_nonneg_left (hweighted m hmN) (Real.rpow_nonneg hmpos.le _)
      _ = (B * K) * (m : ℝ) ^ beta := by ring
  apply not_exists_eventual_poly_bound_squarefreeHalfDirichletPartialSum
    (sigma := (6 / 11 : ℝ)) (alpha := beta) (by norm_num) hbeta0 hbetaLt
  let A : ℝ := 2 * (B * K) * (2 : ℝ) ^ beta
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA0, max N₀ 1, fun N hN => ?_⟩
  rw [show ((6 / 11 : ℝ) : ℂ) = boundaryExteriorPoint by
    norm_num [boundaryExteriorPoint]]
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  have hNsucc : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.le_succ N
  have hpowMono : (N : ℝ) ^ beta ≤ ((N + 1 : ℕ) : ℝ) ^ beta :=
    Real.rpow_le_rpow hNpos.le hNsucc hbeta0
  have hsuccTwo : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hpowTwo : (((N + 1 : ℕ) : ℝ)) ^ beta ≤
      (2 : ℝ) ^ beta * (N : ℝ) ^ beta := by
    calc
      (((N + 1 : ℕ) : ℝ)) ^ beta ≤ (2 * (N : ℝ)) ^ beta :=
        Real.rpow_le_rpow (by positivity) hsuccTwo hbeta0
      _ = (2 : ℝ) ^ beta * (N : ℝ) ^ beta :=
        Real.mul_rpow (by norm_num) hNpos.le
  rw [squarefreeHalfDirichletPartialSum_eq_cesaro_discreteDerivative]
  calc
    ‖((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint -
        (N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
        ((N + 1 : ℕ) : ℝ) * ‖squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint‖ +
          (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ := by
      simpa only [norm_mul, norm_natCast] using norm_sub_le
        (((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint)
        ((N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint)
    _ ≤ (B * K) * ((N + 1 : ℕ) : ℝ) ^ beta +
          (B * K) * (N : ℝ) ^ beta := add_le_add
      (hscaled (N + 1) (by omega) (by omega)) (hscaled N hNN₀ hN1)
    _ ≤ 2 * (B * K) * ((N + 1 : ℕ) : ℝ) ^ beta := by
      nlinarith [mul_le_mul_of_nonneg_left hpowMono hBK0]
    _ ≤ A * (N : ℝ) ^ beta := by
      dsimp [A]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpowTwo
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBK0)

end

end RHTower
