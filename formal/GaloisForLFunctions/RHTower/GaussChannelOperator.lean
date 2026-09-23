import GaloisForLFunctions.RHTower.GaussColumnDecay
import GaloisForLFunctions.RHTower.GaussIterateLogResidue
import GaloisForLFunctions.RHTower.SingularValueLogMean
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.PositiveOperatorPowerMoment
import GaloisForLFunctions.RHTower.GaussPositiveCubicCriticalMass

/-!
# The Gauss channel operator and its singular-value logarithmic mean

The critical power of the quasi-inner block, scaled by the local factor, is a positive compact
operator whose Fourier diagonal has an exact logarithmic mean.  Its columns decay faster than
every power below one, so the diagonal logarithmic mean *is* the singular-value logarithmic
mean.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions ContinuousLinearMap
open GaloisForLFunctions.RHTower
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-! ## Powers of a positive operator are positive -/

theorem isPositive_pow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} (hT : T.IsPositive) (n : ℕ) : (T ^ n).IsPositive := by
  refine ⟨fun x y => hT.inner_pow_left_eq_inner_pow_right n x y, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply,
    hT.inner_pow_left_eq_inner_pow_right n x x]
  exact hT.re_inner_pow_nonneg x n

/-! ## The diagonal block is compact -/

theorem tendsto_norm_gaussSampleValue_cofinite (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun j : ℤ => ‖gaussSampleValue k p j‖) cofinite (nhds 0) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_gaussSampleValue_pow_mul_natAbs_le hm k p
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  set N : ℕ := ⌈C / ε ^ (2 * m)⌉₊ with hNdef
  refine Set.Finite.subset (Set.finite_Icc (-(N : ℤ)) (N : ℤ)) ?_
  intro j hj
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hj
  rw [abs_of_nonneg (norm_nonneg _)] at hj
  rcases eq_or_ne j 0 with rfl | hj0
  · simp only [Set.mem_Icc]
    constructor
    · simp
    · simp
  · have hd := hC j hj0
    have hεm : ε ^ (2 * m) ≤ ‖gaussSampleValue k p j‖ ^ (2 * m) :=
      pow_le_pow_left₀ hε.le hj (2 * m)
    have hnat : (0 : ℝ) ≤ (j.natAbs : ℝ) := by positivity
    have hεpos : (0 : ℝ) < ε ^ (2 * m) := by positivity
    have hbound : ε ^ (2 * m) * (j.natAbs : ℝ) ≤ C := by
      nlinarith [hεm, hd, hnat]
    have hle : (j.natAbs : ℝ) ≤ C / ε ^ (2 * m) := by
      rw [le_div_iff₀ hεpos]
      linarith [hbound]
    have hleN : (j.natAbs : ℝ) ≤ (N : ℝ) := le_trans hle (Nat.le_ceil _)
    have hnatN : j.natAbs ≤ N := by exact_mod_cast hleN
    simp only [Set.mem_Icc]
    omega

theorem isCompactOperator_gaussDiagonalBlock (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    IsCompactOperator (gaussDiagonalBlock hm k p) := by
  refine HTGeometry.isCompactOperator_of_diag_tendsto_cofinite (fourierBasis (T := (1 : ℝ)))
    (c := fun j : ℤ => gaussSampleValue k p j) (fun j => ?_)
    (tendsto_norm_gaussSampleValue_cofinite hm k p)
  have hb : ((fourierBasis (T := (1 : ℝ))) j)
      = (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
    rw [coe_fourierBasis]
  rw [hb]
  exact gaussDiagonalBlock_fourierLp hm k p j

theorem isCompactOperator_gaussQuasiInnerG (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    IsCompactOperator (gaussQuasiInnerG hm k p) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hbase : IsCompactOperator
      (gaussPrimeScaleBlock hp ∘L gaussDiagonalBlock hm k p ∘L
        gaussPrimeScaleInvSqBlock hp ∘L gaussDiagonalBlockStar hm k p ∘L
          gaussPrimeScaleBlock hp) := by
    have h := ((isCompactOperator_gaussDiagonalBlock hm k p).comp_clm
      (gaussPrimeScaleInvSqBlock hp ∘L gaussDiagonalBlockStar hm k p ∘L
        gaussPrimeScaleBlock hp)).clm_comp (gaussPrimeScaleBlock hp)
    simpa [ContinuousLinearMap.coe_comp, Function.comp_def] using h
  exact hbase.smul (((p : ℝ) : ℂ))

theorem isCompactOperator_gaussQuasiInnerGFull (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    IsCompactOperator (gaussQuasiInnerGFull hm k p) := by
  rw [gaussQuasiInnerGFull_eq]
  exact (isCompactOperator_gaussQuasiInnerG hm k p).smul (((gaussArchScale m ^ 2 : ℝ) : ℂ))

/-! ## The channel operator -/

/-- The Gauss channel operator: the critical power of the quasi-inner block weighted by the
local factor `((p-1)/p)^{2m}`. -/
def gaussChannelOperator (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((gaussLocalFactorWeight m p : ℝ) : ℂ) • (gaussQuasiInnerGFull hm k p ^ m)

theorem gaussChannelOperator_isPositive (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    (gaussChannelOperator hm k p).IsPositive := by
  rw [gaussChannelOperator]
  refine (isPositive_pow (gaussQuasiInnerGFull_isPositive hm k p) m).smul_of_nonneg ?_
  rw [Complex.nonneg_iff]
  exact ⟨(gaussLocalFactorWeight_pos m p).le, rfl⟩

theorem gaussChannelOperator_nonneg (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    (0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) ≤ gaussChannelOperator hm k p := by
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact gaussChannelOperator_isPositive hm k p

theorem isCompactOperator_gaussChannelOperator (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    IsCompactOperator (gaussChannelOperator hm k p) := by
  -- `RHTower.isCompactOperator_pow` (Suzuki lane) is the general statement; the single instance
  -- needed here is inlined so that the Gauss chain stays independent of that import.
  have hpowgen : ∀ (A : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))), IsCompactOperator A →
      ∀ n : ℕ, IsCompactOperator (A ^ (n + 1)) := by
    intro A hA n
    induction n with
    | zero => simpa using hA
    | succ j ih =>
        have hmul : ⇑(A ^ (j + 1 + 1)) = ⇑(A ^ (j + 1)) ∘ ⇑A := by
          ext x
          simp [pow_succ]
        rw [hmul]
        exact ih.comp_clm A
  obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hbase : IsCompactOperator (gaussQuasiInnerGFull hm k p ^ m) := by
    have h := hpowgen _ (isCompactOperator_gaussQuasiInnerGFull hm k p) r
    rw [← hr] at h
    exact h
  exact hbase.smul (((gaussLocalFactorWeight m p : ℝ) : ℂ))

/-! ## The band decomposition of a symmetric sum -/

theorem sum_Icc_eq_zero_add_sum_range (f : ℤ → ℝ) (M : ℕ) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f j
      = f 0 + ∑ n ∈ Finset.range M, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  classical
  induction M with
  | zero => simp
  | succ M ih =>
      have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ)
          = insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        push_cast
        omega
      have hmem1 : ((M : ℤ) + 1) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      have hmem2 : (-((M : ℤ) + 1))
          ∉ insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hmem2, Finset.sum_insert hmem1, ih, Finset.sum_range_succ]
      ring

/-! ## The diagonal of the channel operator -/

theorem inner_gaussChannelOperator_fourierLp (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℤ) :
    (inner ℂ (fourierLp 2 j) (gaussChannelOperator hm k p (fourierLp 2 j)) : ℂ)
      = ((gaussLocalFactorWeight m p : ℝ) : ℂ) *
        inner ℂ (fourierLp 2 j) ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 j)) := by
  rw [gaussChannelOperator]
  show (inner ℂ (fourierLp 2 j)
      (((gaussLocalFactorWeight m p : ℝ) : ℂ) •
        ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 j))) : ℂ) = _
  rw [inner_smul_right]

theorem norm_gaussChannelOperator_fourierLp (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ) :
    ‖gaussChannelOperator hm k p (fourierLp 2 n)‖
      = gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m
        * ‖(gaussQuasiInnerG hm k p ^ m) (fourierLp 2 n)‖ := by
  have harch : (0 : ℝ) ≤ (gaussArchScale m ^ 2) ^ m := by positivity
  rw [gaussChannelOperator, gaussQuasiInnerGFull_eq, smul_pow]
  show ‖((gaussLocalFactorWeight m p : ℝ) : ℂ) •
      ((((gaussArchScale m ^ 2 : ℝ) : ℂ) ^ m) • ((gaussQuasiInnerG hm k p ^ m)
        (fourierLp 2 n)))‖ = _
  rw [norm_smul, norm_smul, ← Complex.ofReal_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (gaussLocalFactorWeight_pos m p).le, abs_of_nonneg harch]
  ring

/-! ## The band logarithmic mean -/

theorem tendsto_gaussChannelOperator_band_logMean (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        RCLike.re (inner ℂ ((fourierBasis (T := (1 : ℝ))) j)
          (gaussChannelOperator (le_trans one_le_two hm2) k p
            ((fourierBasis (T := (1 : ℝ))) j)) : ℂ)) / Real.log (M : ℝ))
      atTop (nhds (gaussChannelResidue m p)) := by
  have hm : (1 : ℕ) ≤ m := le_trans one_le_two hm2
  set g : ℤ → ℂ := fun j =>
    inner ℂ (fourierLp 2 j) ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 j)) with hgdef
  set f : ℤ → ℝ := fun j =>
    RCLike.re (inner ℂ ((fourierBasis (T := (1 : ℝ))) j)
      (gaussChannelOperator hm k p ((fourierBasis (T := (1 : ℝ))) j)) : ℂ) with hfdef
  have hfval : ∀ j : ℤ, f j = gaussLocalFactorWeight m p * (g j).re := by
    intro j
    have hb : ((fourierBasis (T := (1 : ℝ))) j)
        = (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
      rw [coe_fourierBasis]
    rw [hfdef]
    simp only [hb]
    rw [inner_gaussChannelOperator_fourierLp hm k p j]
    exact Complex.re_ofReal_mul (gaussLocalFactorWeight m p) (g j)
  have hbase := tendsto_gaussLocalDiagonal_pow_logResidue hm2 k p
  have hre : Tendsto (fun N : ℕ =>
      (((gaussLocalFactorWeight m p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
          (Real.log (N : ℝ) : ℂ))).re) atTop (nhds (gaussChannelResidue m p)) := by
    have h := (Complex.continuous_re.tendsto _).comp hbase
    exact h
  have hsimp : ∀ N : ℕ,
      (((gaussLocalFactorWeight m p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
          (Real.log (N : ℝ) : ℂ))).re
        = (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))) /
            Real.log (N : ℝ) := by
    intro N
    have hdiv : ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
        (Real.log (N : ℝ) : ℂ)).re
        = (∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))).re
          / Real.log (N : ℝ) := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul]
      ring
    have hterm : ∀ n ∈ Finset.range N,
        (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1))).re
          = (g ((n : ℤ) + 1)).re + (g (-((n : ℤ) + 1))).re := fun n _ => Complex.add_re _ _
    have hsum2 : (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))))
        = gaussLocalFactorWeight m p *
          ∑ x ∈ Finset.range N, ((g ((x : ℤ) + 1)).re + (g (-((x : ℤ) + 1))).re) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hfval, hfval]
      ring
    rw [Complex.re_ofReal_mul, hdiv, Complex.re_sum, Finset.sum_congr rfl hterm, hsum2]
    ring
  have hmid : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))) / Real.log (N : ℝ))
      atTop (nhds (gaussChannelResidue m p)) := hre.congr fun N => hsimp N
  have hzero : Tendsto (fun N : ℕ => f 0 / Real.log (N : ℝ)) atTop (nhds 0) :=
    ContinuousLinearMap.tendsto_const_div_log_natCast (f 0)
  have hsum := hzero.add hmid
  rw [zero_add] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div, ← sum_Icc_eq_zero_add_sum_range f N]

/-! ## The column decay of the channel operator -/

theorem exists_norm_gaussChannelOperator_fourierBasis_le (hm : 1 ≤ m) (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      ‖gaussChannelOperator hm k p ((fourierBasis (T := (1 : ℝ))) n)‖
        ≤ C * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  obtain ⟨C, hC0, hC⟩ := exists_norm_gaussQuasiInnerG_pow_fourierLp_le hm hm2 k p hp hρ
  have hw : (0 : ℝ) ≤ gaussLocalFactorWeight m p := (gaussLocalFactorWeight_pos m p).le
  have harch : (0 : ℝ) ≤ (gaussArchScale m ^ 2) ^ m := by positivity
  refine ⟨gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m * C, by positivity,
    fun n hn => ?_⟩
  have hb : ((fourierBasis (T := (1 : ℝ))) n)
      = (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
    rw [coe_fourierBasis]
  rw [hb, norm_gaussChannelOperator_fourierLp hm k p n]
  have h := hC n hn
  have hK : (0 : ℝ) ≤ gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m := by positivity
  calc gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m
        * ‖(gaussQuasiInnerG hm k p ^ m) (fourierLp 2 n)‖
      ≤ gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m
        * (C * ((n.natAbs : ℝ)) ^ (-1 + ρ)) := mul_le_mul_of_nonneg_left h hK
    _ = gaussLocalFactorWeight m p * (gaussArchScale m ^ 2) ^ m * C
        * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by ring

/-! ## The singular-value logarithmic mean of the channel operator -/

theorem tendsto_sum_singVal_gaussChannelOperator (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        singVal (gaussChannelOperator (le_trans one_le_two hm2) k p) n) / Real.log (N : ℝ))
      atTop (nhds (gaussChannelResidue m p)) := by
  have hm : (1 : ℕ) ≤ m := le_trans one_le_two hm2
  refine ContinuousLinearMap.tendsto_sum_singVal_div_log_of_diagonal
    (fourierBasis (T := (1 : ℝ)))
    (isCompactOperator_gaussChannelOperator hm k p)
    (gaussChannelOperator_nonneg hm k p)
    (tendsto_gaussChannelOperator_band_logMean hm2 k p) (fun δ hδ => ?_)
  exact exists_norm_gaussChannelOperator_fourierBasis_le hm hm2 k p hδ

/-! ## Dixmier-ideal membership from the logarithmic mean -/

theorem isDixmier_of_tendsto_logMean {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} {R : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, singVal T n) / Real.log (N : ℝ)) atTop (nhds R)) :
    ContinuousLinearMap.IsDixmier T := by
  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, singVal T n with hSdef
  have hS0 : ∀ N, 0 ≤ S N := fun N => Finset.sum_nonneg fun n _ => singVal_nonneg T n
  have hSmono : ∀ a b : ℕ, a ≤ b → S a ≤ S b := by
    intro a b hab
    have hsub : Finset.range a ⊆ Finset.range b := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => singVal_nonneg T n)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 (R + 1) (by linarith))
  set M₀ : ℕ := max N₀ 2 with hM₀
  refine ⟨max (R + 1) (S M₀), le_max_of_le_right (hS0 M₀), fun N hN => ?_⟩
  have hC0 : (0 : ℝ) ≤ max (R + 1) (S M₀) := le_max_of_le_right (hS0 M₀)
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hN
  show S N ≤ max (R + 1) (S M₀) * (1 + Real.log (N : ℝ))
  rcases lt_or_ge N M₀ with hlt | hge
  · have h1 : S N ≤ S M₀ := hSmono N M₀ hlt.le
    have h2 : S M₀ ≤ max (R + 1) (S M₀) := le_max_right _ _
    nlinarith [h1, h2, hlogN, hC0]
  · have hN2 : 2 ≤ N := le_trans (le_max_right N₀ 2) hge
    have hlogpos : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      linarith
    have hlt' : S N / Real.log (N : ℝ) < R + 1 := hN₀ N (le_trans (le_max_left N₀ 2) hge)
    have h3 : S N < (R + 1) * Real.log (N : ℝ) := by
      rw [div_lt_iff₀ hlogpos] at hlt'
      exact hlt'
    have h4 : (R + 1) ≤ max (R + 1) (S M₀) := le_max_left _ _
    nlinarith [h3, h4, hlogpos, hC0]

/-! ## The closed statement -/

theorem isDixmier_gaussChannelOperator (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ContinuousLinearMap.IsDixmier (gaussChannelOperator (le_trans one_le_two hm2) k p) :=
  isDixmier_of_tendsto_logMean (tendsto_sum_singVal_gaussChannelOperator hm2 k p)

/-- **The Dixmier trace of the Gauss channel operator.**  The logarithmic mean of the singular
values of `((p-1)/p)^{2m} · G_full^m` is the arithmetic residue
`2 (p-1)^{2m} (p^m-1)^(2 : ℕ) / (p^{2m} m^(2 : ℕ) log p)`. -/
theorem hasSchattenLogResidue_gaussChannelOperator (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    HasSchattenLogResidue 1 (gaussChannelOperator (le_trans one_le_two hm2) k p)
      (gaussChannelResidue m p) := by
  have hm : (1 : ℕ) ≤ m := le_trans one_le_two hm2
  have hcpt := isCompactOperator_gaussChannelOperator hm k p
  have hbase := tendsto_sum_singVal_gaussChannelOperator hm2 k p
  -- the ratio of the two logarithmic scales
  have hstep : Tendsto (fun N : ℕ =>
      Real.log (((N + 1 : ℕ) : ℕ) : ℝ) / Real.log (N : ℝ)) atTop (nhds 1) := by
    refine ContinuousLinearMap.tendsto_log_div_log_of_bounds (f := fun N : ℕ => N + 1)
      (α := 1) (β := Real.log 2) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h := Real.log_le_log hNpos hle
      have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hle : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        push_cast
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h
      linarith
  have hinv : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) / Real.log (((N : ℝ)) + 1)) atTop (nhds 1) := by
    have h := hstep.inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr fun N => ?_
    rw [inv_div]
    push_cast
    rfl
  have hprod := hbase.mul hinv
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hsp : schattenPowerPartialSum 1
      (gaussChannelOperator (le_trans one_le_two hm2) k p) N
      = ∑ n ∈ Finset.range N,
        singVal (gaussChannelOperator (le_trans one_le_two hm2) k p) n := by
    rw [schattenPowerPartialSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.rpow_one, approxNumber_eq_singVal hcpt n]
  rw [hsp]
  field_simp

end

end RHTower
