import GaloisForLFunctions.HTGeometry.CentralBinomialSeries
import GaloisForLFunctions.RHTower.SuzukiPrimeNormalCoronaComparison
import GaloisForLFunctions.RHTower.SuzukiGammaCoronaSequence

/-!
# The binomial expansion of the prime-normal cross-section

The binomial resolvent symbol `(1 - t/(2L))^{-1/2}` is the central binomial series in `t/(2L)`,
which converges uniformly on the spectrum of a self-adjoint element once `‖T‖ ≤ L`, since then
`|t/(2L)| ≤ 1/2`.  Continuity of the functional calculus in the symbol therefore turns the scalar
series into the operator series

`(1 - T/(2L))^{-1/2} = ∑_k [C(2k,k)/4^k] (2L)^{-k} T^k`,

so every prime descendant of the cross-section appears with its own grade and no path is deleted.
-/

open Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The binomial symbol is the negative half power of the shifted coordinate. -/
theorem binomialSymbol_eq_rpow {L t : ℝ} (h : 0 < 1 - t / (2 * L)) :
    binomialSymbol L t = (1 - t / (2 * L)) ^ (-(1 : ℝ) / 2) := by
  rw [binomialSymbol, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg h.le, ← Real.sqrt_eq_rpow, one_div]

/-- The truncated binomial series. -/
def binomialPartial (L : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((Nat.centralBinom k : ℝ) / 4 ^ k) * (t / (2 * L)) ^ k

/-- The dominating geometric series of the binomial coefficients. -/
theorem summable_centralBinom_half :
    Summable (fun k : ℕ => ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2 : ℝ) ^ k) :=
  (hasSum_centralBinom (x := (1 / 2 : ℝ)) (by rw [abs_of_pos] <;> norm_num)).summable

/-- The uniform tail bound of the binomial series on the admissible interval. -/
theorem norm_binomialSymbol_sub_partial_le {L : ℝ} (hL0 : 0 < L) {c : ℝ} (hc : c ≤ L) {t : ℝ}
    (ht : t ∈ Icc (-c) c) (N : ℕ) :
    ‖binomialSymbol L t - binomialPartial L N t‖
      ≤ ∑' i : ℕ, ((Nat.centralBinom (i + N) : ℝ) / 4 ^ (i + N)) * (1 / 2 : ℝ) ^ (i + N) := by
  have habs : |t / (2 * L)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * L), div_le_div_iff₀ (by positivity)
      (by norm_num)]
    have h1 : |t| ≤ c := abs_le.mpr ⟨ht.1, ht.2⟩
    nlinarith [h1, hc, hL0]
  have hlt : |t / (2 * L)| < 1 := by linarith
  have hpos : 0 < 1 - t / (2 * L) := by
    have hb := abs_le.mp habs
    linarith [hb.1, hb.2]
  set a : ℕ → ℝ := fun k => ((Nat.centralBinom k : ℝ) / 4 ^ k) * (t / (2 * L)) ^ k with ha
  set M : ℕ → ℝ := fun k => ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2 : ℝ) ^ k with hM
  have hbound : ∀ k, ‖a k‖ ≤ M k := by
    intro k
    rw [ha, hM]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.centralBinom k : ℝ) / 4 ^ k)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) habs k) (by positivity)
  have hMsum : Summable M := summable_centralBinom_half
  have hasum : Summable a := Summable.of_norm_bounded hMsum hbound
  have hsumval : ∑' k : ℕ, a k = binomialSymbol L t := by
    rw [binomialSymbol_eq_rpow hpos]
    exact (hasSum_centralBinom hlt).tsum_eq
  have hsplit : (∑ k ∈ Finset.range N, a k) + ∑' i : ℕ, a (i + N) = ∑' k : ℕ, a k :=
    hasum.sum_add_tsum_nat_add N
  have hpartial : binomialPartial L N t = ∑ k ∈ Finset.range N, a k := rfl
  have heq : binomialSymbol L t - binomialPartial L N t = ∑' i : ℕ, a (i + N) := by
    rw [← hsumval, hpartial, ← hsplit]
    ring
  rw [heq]
  have hMshift : Summable (fun i : ℕ => M (i + N)) := (summable_nat_add_iff N).mpr hMsum
  have hnormshift : Summable (fun i : ℕ => ‖a (i + N)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hbound (i + N)) hMshift
  refine le_trans (norm_tsum_le_tsum_norm hnormshift) ?_
  exact Summable.tsum_le_tsum (fun i => hbound (i + N)) hnormshift hMshift

omit [CompleteSpace A] [NormOneClass A] in
/-- The functional calculus of the truncated series is the truncated operator series. -/
theorem cfc_binomialPartial (T : A) (hT : IsSelfAdjoint T) (L : ℝ) (N : ℕ) :
    cfc (binomialPartial L N) T
      = ∑ k ∈ Finset.range N, ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k := by
  have hlin : cfc (fun t : ℝ => t / (2 * L)) T = (2 * L)⁻¹ • T := by
    have hfun : (fun t : ℝ => t / (2 * L)) = fun t : ℝ => (2 * L)⁻¹ * t := by
      funext t
      rw [div_eq_inv_mul]
    rw [hfun, cfc_const_mul ((2 * L)⁻¹) (fun t : ℝ => t) T (by fun_prop), cfc_id' ℝ T hT]
  have hterm : ∀ k : ℕ, cfc (fun t : ℝ => ((Nat.centralBinom k : ℝ) / 4 ^ k)
      * (t / (2 * L)) ^ k) T
      = ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k := by
    intro k
    rw [cfc_const_mul ((Nat.centralBinom k : ℝ) / 4 ^ k) (fun t : ℝ => (t / (2 * L)) ^ k) T
        (by fun_prop),
      cfc_pow (fun t : ℝ => t / (2 * L)) k T (by fun_prop) hT, hlin, smul_pow, smul_smul]
    congr 1
    rw [inv_pow, ← div_eq_mul_inv, div_div]
  have hfunsum : binomialPartial L N
      = ∑ k ∈ Finset.range N,
        (fun t : ℝ => ((Nat.centralBinom k : ℝ) / 4 ^ k) * (t / (2 * L)) ^ k) := by
    funext t
    rw [binomialPartial, Finset.sum_apply]
  rw [hfunsum, cfc_sum _ T _ (fun k _ => by fun_prop)]
  exact Finset.sum_congr rfl fun k _ => hterm k

/-- **The binomial expansion of the resolvent symbol.** -/
theorem hasSum_cfc_binomialSymbol (T : A) (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ ≤ L)
    (hL0 : 0 < L) :
    HasSum (fun k : ℕ => ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k)
      (cfc (binomialSymbol L) T) := by
  have hspec : spectrum ℝ T ⊆ Icc (-‖T‖) ‖T‖ := by
    intro x hx
    have hxle : ‖x‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hx
    have hxabs : |x| ≤ ‖T‖ := by simpa [Real.norm_eq_abs] using hxle
    exact abs_le.mp hxabs
  have hcontS : ContinuousOn (binomialSymbol L) (spectrum ℝ T) :=
    (continuousOn_binomialSymbol hL0 hL).mono hspec
  have hcontP : ∀ N : ℕ, ContinuousOn (binomialPartial L N) (spectrum ℝ T) := by
    intro N
    show ContinuousOn (fun t : ℝ => ∑ k ∈ Finset.range N,
      ((Nat.centralBinom k : ℝ) / 4 ^ k) * (t / (2 * L)) ^ k) (spectrum ℝ T)
    fun_prop
  have hnormbd : ∀ k : ℕ, ‖((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k‖
      ≤ ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2 : ℝ) ^ k := by
    intro k
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k))]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hTk : ‖T ^ k‖ ≤ ‖T‖ ^ k := norm_pow_le' T hk
      have hratio : ‖T‖ ^ k / (2 * L) ^ k ≤ (1 / 2 : ℝ) ^ k := by
        rw [← div_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      calc (Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k) * ‖T ^ k‖
          ≤ (Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k) * ‖T‖ ^ k :=
            mul_le_mul_of_nonneg_left hTk (by positivity)
        _ = ((Nat.centralBinom k : ℝ) / 4 ^ k) * (‖T‖ ^ k / (2 * L) ^ k) := by
            rw [div_mul_eq_div_div]
            ring
        _ ≤ ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
  have hsummable : Summable
      (fun k : ℕ => ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k) :=
    Summable.of_norm_bounded summable_centralBinom_half hnormbd
  refine (hsummable.hasSum_iff_tendsto_nat).mpr ?_
  have hdiff : ∀ N : ℕ,
      ‖(∑ k ∈ Finset.range N, ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k)
          - cfc (binomialSymbol L) T‖
        ≤ ∑' i : ℕ, ((Nat.centralBinom (i + N) : ℝ) / 4 ^ (i + N)) * (1 / 2 : ℝ) ^ (i + N) := by
    intro N
    rw [← cfc_binomialPartial T hT L N, ← norm_neg, neg_sub,
      ← cfc_sub (binomialSymbol L) (binomialPartial L N) T hcontS (hcontP N)]
    refine norm_cfc_le (by positivity) fun x hx => ?_
    exact norm_binomialSymbol_sub_partial_le hL0 hL (hspec hx) N
  have htail : Filter.Tendsto
      (fun N : ℕ => ∑' i : ℕ, ((Nat.centralBinom (i + N) : ℝ) / 4 ^ (i + N))
        * (1 / 2 : ℝ) ^ (i + N)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add (fun k : ℕ => ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2 : ℝ) ^ k)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ htail
  filter_upwards with N
  exact hdiff N

section CrossSection

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- **The prime-normal cross-section is the binomial series of its prime descendants.**  Grade
zero is the pure half-log term and every higher grade carries one more power of the adjacency. -/
theorem hasSum_primeNormalSection (T : X →L[ℂ] X) (hT : IsSelfAdjoint T) (β : X)
    {L : ℝ} (hL : ‖T‖ ≤ L) (hL0 : 0 < L) :
    HasSum (fun k : ℕ => ((Nat.centralBinom k : ℝ) / 8 ^ k * L ^ (-(k : ℝ) - 1 / 2))
        • ((T ^ k) β))
      (GaloisForLFunctions.RHTower.primeNormalSection T β L) := by
  have hcfc := hasSum_cfc_binomialSymbol T hT hL hL0
  have happ := hcfc.map (ContinuousLinearMap.apply ℂ X β)
    (ContinuousLinearMap.apply ℂ X β).continuous
  have hval : ∀ k : ℕ,
      ((ContinuousLinearMap.apply ℂ X β) ∘
        fun k : ℕ => ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • T ^ k) k
        = ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • ((T ^ k) β) := by
    intro k
    rfl
  have happ' : HasSum
      (fun k : ℕ => ((Nat.centralBinom k : ℝ) / (4 ^ k * (2 * L) ^ k)) • ((T ^ k) β))
      ((cfc (binomialSymbol L) T) β) := happ.congr_fun hval
  have hscaled := happ'.const_smul (L ^ (-(1 : ℝ) / 2))
  refine hscaled.congr_fun ?_
  intro k
  rw [smul_smul]
  congr 1
  have h8 : (4 : ℝ) ^ k * (2 * L) ^ k = 8 ^ k * L ^ k := by
    rw [mul_pow, ← mul_assoc, ← mul_pow]
    norm_num
  have hLk : (L : ℝ) ^ k = L ^ (k : ℝ) := (Real.rpow_natCast L k).symm
  have hLrpos : (0 : ℝ) < L ^ (k : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hsplit : L ^ (-(k : ℝ) - 1 / 2) = (L ^ (k : ℝ))⁻¹ * L ^ (-(1 : ℝ) / 2) := by
    rw [show (-(k : ℝ) - 1 / 2) = (-(k : ℝ)) + (-(1 : ℝ) / 2) by ring,
      Real.rpow_add hL0, Real.rpow_neg hL0.le]
  rw [h8, hLk, hsplit]
  have h8ne : (8 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

end CrossSection

end

end RHTower
