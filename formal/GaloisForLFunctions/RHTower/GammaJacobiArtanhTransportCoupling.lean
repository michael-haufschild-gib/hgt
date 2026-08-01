import GaloisForLFunctions.RHTower.GammaOddJacobiCoherentCapacity
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorDiracKreinEdge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Odd Gamma--Jacobi head realization of the successor transport current

The coherent odd Gamma--Jacobi residual and the successor Dirac--Krein current previously lived on
separate coordinate systems.  This module gives them one absolute Jacobi coordinate.  A fixed,
source-independent incidence row applied to the first `K` normalized odd Gamma--Jacobi modes is the
truncated artanh coordinate

`T_K(t) = sum_{k<K} tanh(t)^(2k+1)/(2k+1)`.

Its derivative defect is exactly `tanh(t)^(2K)`.  Replacing the logarithmic coordinate in the
source-edge Dirac--Krein lift by `T_K` therefore gives an exact finite-mode current.  At every fixed
source and jet aperture these currents converge to the principal-relative successor matrix.  The
same cutoff complement is the zero-padded odd Gamma--Jacobi residual already used by the coherent
capacity theorem.

This is a common-coordinate coupling, not an RH proof: completed Euler cyclic reading and fibre
orientation remain open.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Fixed incidence row converting normalized odd Gamma--Jacobi modes to the log coordinate. -/
def gammaOddJacobiLogIncidence (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k /
    ((((2 * k + 1 : ℕ) : ℝ)) *
      semilocalArchimedeanJacobiNormalization (2 * k + 1))

/-- First `K` absolute odd Jacobi modes read through the fixed log-incidence row. -/
def gammaOddJacobiLogHead (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K,
    gammaOddJacobiLogIncidence k * gammaOddJacobiCoefficient k t /
      semilocalArchimedeanCharacteristic t

/-- One incidence coordinate cancels the Jacobi normalization, Gamma characteristic, and phase. -/
theorem gammaOddJacobiLogIncidence_mul_normalizedCoefficient
    (k : ℕ) (t : ℝ) :
    gammaOddJacobiLogIncidence k * gammaOddJacobiCoefficient k t /
        semilocalArchimedeanCharacteristic t =
      Real.tanh t ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ)) := by
  have hc := (semilocalArchimedeanJacobiNormalization_pos (2 * k + 1)).ne'
  have hp := (semilocalArchimedeanCharacteristic_pos t).ne'
  have hs : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [gammaOddJacobiLogIncidence, gammaOddJacobiCoefficient]
  field_simp [hc, hp]
  rw [pow_two, hs]
  ring

/-- The Jacobi head is literally the truncated odd artanh series. -/
theorem gammaOddJacobiLogHead_eq (K : ℕ) (t : ℝ) :
    gammaOddJacobiLogHead K t =
      ∑ k ∈ Finset.range K,
        Real.tanh t ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ)) := by
  apply Finset.sum_congr rfl
  intro k hk
  exact gammaOddJacobiLogIncidence_mul_normalizedCoefficient k t

/-- Exact finite-capacity connection law: missing log derivative is one geometric tail monomial. -/
theorem hasDerivAt_gammaOddJacobiLogHead (K : ℕ) (t : ℝ) :
    HasDerivAt (gammaOddJacobiLogHead K)
      (1 - Real.tanh t ^ (2 * K)) t := by
  have hxmem : Real.tanh t ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  have hraw :=
    (Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range K
      hxmem.1 hxmem.2).comp t (hasDerivAt_tanh_one_sub_sq t)
  have hden : 1 - Real.tanh t ^ 2 ≠ 0 := by
    nlinarith [Real.neg_one_lt_tanh t, Real.tanh_lt_one t]
  have hfun :
      ((fun x => 1 / 2 * Real.log ((1 + x) / (1 - x)) -
          ∑ i ∈ Finset.range K, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ∘ Real.tanh) =
        fun y => y - gammaOddJacobiLogHead K y := by
    funext y
    rw [gammaOddJacobiLogHead_eq]
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    rw [← Real.artanh_eq_half_log (show Real.tanh y ∈ Set.Icc (-1) 1 by
      exact ⟨(Real.neg_one_lt_tanh y).le, (Real.tanh_lt_one y).le⟩),
      Real.artanh_tanh]
  rw [hfun] at hraw
  have hscalar :
      (Real.tanh t ^ 2) ^ K / (1 - Real.tanh t ^ 2) *
          (1 - Real.tanh t ^ 2) = Real.tanh t ^ (2 * K) := by
    rw [pow_mul]
    field_simp [hden]
  rw [hscalar] at hraw
  have hrem : HasDerivAt (fun y => y - gammaOddJacobiLogHead K y)
      (Real.tanh t ^ (2 * K)) t := hraw
  have h := (hasDerivAt_id t).sub hrem
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  change gammaOddJacobiLogHead K y = y - (y - gammaOddJacobiLogHead K y)
  ring

/-- Cofinal odd Jacobi capacity reconstructs the logarithmic coordinate pointwise. -/
theorem tendsto_gammaOddJacobiLogHead (t : ℝ) :
    Tendsto (fun K => gammaOddJacobiLogHead K t) atTop (nhds t) := by
  have hx : |Real.tanh t| < 1 :=
    abs_lt.2 ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  have hbound (K : ℕ) :
      |t - gammaOddJacobiLogHead K t| ≤
        |Real.tanh t| ^ (2 * K + 1) / (1 - Real.tanh t ^ 2) := by
    rw [gammaOddJacobiLogHead_eq]
    calc
      |t - ∑ k ∈ Finset.range K,
          Real.tanh t ^ (2 * k + 1) / ↑(2 * k + 1)| =
          |Real.artanh (Real.tanh t) - ∑ k ∈ Finset.range K,
            Real.tanh t ^ (2 * k + 1) / ↑(2 * k + 1)| := by
            rw [Real.artanh_tanh]
      _ = |1 / 2 * Real.log ((1 + Real.tanh t) / (1 - Real.tanh t)) -
          ∑ k ∈ Finset.range K,
            Real.tanh t ^ (2 * k + 1) / ↑(2 * k + 1)| := by
            rw [Real.artanh_eq_half_log (show Real.tanh t ∈ Set.Icc (-1) 1 by
              exact ⟨(Real.neg_one_lt_tanh t).le, (Real.tanh_lt_one t).le⟩)]
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
          Real.sum_range_sub_log_div_le hx K
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hden : 0 < 1 - Real.tanh t ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 hx)
  have hpow : Tendsto (fun K : ℕ => |Real.tanh t| ^ (2 * K + 1)) atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hx
    have hindex : Tendsto (fun K : ℕ => 2 * K + 1) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      exact eventually_atTop.2 ⟨b, fun K hK => by omega⟩
    exact hbase.comp hindex
  have hdiv := hpow.div_const (1 - Real.tanh t ^ 2)
  have hevent : ∀ᶠ K : ℕ in atTop,
      |Real.tanh t| ^ (2 * K + 1) / (1 - Real.tanh t ^ 2) < ε := by
    have := (Metric.tendsto_nhds.1 hdiv) ε hε
    filter_upwards [this] with K hK
    simpa [Real.dist_eq, abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg _) _)
      hden.le), abs_of_pos hden] using hK
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  exact ⟨N, fun K hK => by
    rw [Real.dist_eq, abs_sub_comm]
    exact (hbound K).trans_lt (hN K hK)⟩

/-- First-order exchange lift after replacing `t` by its first `K` Jacobi modes. -/
def gammaOddJacobiHeadTransportJet (K i : ℕ) (t : ℝ) : ℝ × ℝ :=
  (((i + 1 : ℕ) : ℝ) * gammaOddJacobiLogHead K t ^ i *
      (1 - Real.tanh t ^ (2 * K)),
    gammaOddJacobiLogHead K t ^ (i + 1))

theorem hasDerivAt_gammaOddJacobiHeadTransportValue
    (K i : ℕ) (t : ℝ) :
    HasDerivAt (fun y => gammaOddJacobiLogHead K y ^ (i + 1))
      (gammaOddJacobiHeadTransportJet K i t).1 t := by
  have h := (hasDerivAt_gammaOddJacobiLogHead K t).pow (i + 1)
  exact h

theorem exchangePair_gammaOddJacobiHeadTransportJet
    (K i j : ℕ) (t : ℝ) :
    HTGeometry.exchangePair
        (gammaOddJacobiHeadTransportJet K i t)
        (gammaOddJacobiHeadTransportJet K j t) =
      (((i + j + 2 : ℕ) : ℝ) *
        gammaOddJacobiLogHead K t ^ (i + j + 1) *
          (1 - Real.tanh t ^ (2 * K))) := by
  have h₁ : gammaOddJacobiLogHead K t ^ i *
      gammaOddJacobiLogHead K t ^ (j + 1) =
      gammaOddJacobiLogHead K t ^ (i + j + 1) := by
    rw [← pow_add]
    congr 1
  have h₂ : gammaOddJacobiLogHead K t ^ (i + 1) *
      gammaOddJacobiLogHead K t ^ j =
      gammaOddJacobiLogHead K t ^ (i + j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [HTGeometry.exchangePair, gammaOddJacobiHeadTransportJet]
  calc
    (((i + 1 : ℕ) : ℝ) * gammaOddJacobiLogHead K t ^ i *
          (1 - Real.tanh t ^ (2 * K))) *
          gammaOddJacobiLogHead K t ^ (j + 1) +
        gammaOddJacobiLogHead K t ^ (i + 1) *
          (((j + 1 : ℕ) : ℝ) * gammaOddJacobiLogHead K t ^ j *
            (1 - Real.tanh t ^ (2 * K))) =
        ((((i + 1 : ℕ) : ℝ) *
            (gammaOddJacobiLogHead K t ^ i *
              gammaOddJacobiLogHead K t ^ (j + 1))) +
          (((j + 1 : ℕ) : ℝ) *
            (gammaOddJacobiLogHead K t ^ (i + 1) *
              gammaOddJacobiLogHead K t ^ j))) *
            (1 - Real.tanh t ^ (2 * K)) := by ring
    _ = _ := by rw [h₁, h₂]; push_cast; ring

/-- Exact finite-mode Dirac--Stokes current on one logarithmic source edge. -/
theorem intervalIntegral_exchangePair_gammaOddJacobiHeadTransportJet
    (K i j : ℕ) (x y : ℝ) :
    (∫ t in x..y,
      HTGeometry.exchangePair
        (gammaOddJacobiHeadTransportJet K i t)
        (gammaOddJacobiHeadTransportJet K j t)) =
      gammaOddJacobiLogHead K y ^ (i + j + 2) -
        gammaOddJacobiLogHead K x ^ (i + j + 2) := by
  let F : ℝ → ℝ := fun t => gammaOddJacobiLogHead K t ^ (i + j + 2)
  let dF : ℝ → ℝ := fun t =>
    (((i + j + 2 : ℕ) : ℝ) *
      gammaOddJacobiLogHead K t ^ (i + j + 1) *
        (1 - Real.tanh t ^ (2 * K)))
  have hF (t : ℝ) : HasDerivAt F (dF t) t := by
    have h := (hasDerivAt_gammaOddJacobiLogHead K t).pow (i + j + 2)
    apply h.congr_deriv
    dsimp only [dF]
    push_cast
    ring
  have hderiv : deriv F = dF := by
    funext t
    exact (hF t).deriv
  have hhead : Continuous (gammaOddJacobiLogHead K) := by
    have htanh : Continuous Real.tanh :=
      continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_tanh_one_sub_sq t).continuousAt
    rw [show gammaOddJacobiLogHead K = fun t =>
        ∑ k ∈ Finset.range K,
          Real.tanh t ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ)) by
      funext t
      exact gammaOddJacobiLogHead_eq K t]
    apply continuous_finsetSum (Finset.range K)
    intro k hk
    exact (htanh.pow (2 * k + 1)).div_const _
  have hdF : Continuous dF := by
    have htanh : Continuous Real.tanh :=
      continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_tanh_one_sub_sq t).continuousAt
    dsimp only [dF]
    exact (continuous_const.mul (hhead.pow (i + j + 1))).mul
      (continuous_const.sub (htanh.pow (2 * K)))
  have hfund := intervalIntegral.integral_deriv_eq_sub'
    (a := x) (b := y) F hderiv
      (fun t _ => (hF t).differentiableAt) hdF.continuousOn
  calc
    (∫ t in x..y,
        HTGeometry.exchangePair
          (gammaOddJacobiHeadTransportJet K i t)
          (gammaOddJacobiHeadTransportJet K j t)) =
        ∫ t in x..y, dF t :=
      intervalIntegral.integral_congr fun t _ =>
        exchangePair_gammaOddJacobiHeadTransportJet K i j t
    _ = _ := by simpa only [F] using hfund

/-- Finite source and jet aperture of the odd-Jacobi-head exchange current. -/
def finiteVonMangoldtGammaJacobiHeadKreinGram
    (K M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ p : Fin M,
    finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
      (∫ t in Real.log (((p : ℕ) + 2 : ℕ) : ℝ)..
          Real.log (((p : ℕ) + 3 : ℕ) : ℝ),
        HTGeometry.exchangePair
          (gammaOddJacobiHeadTransportJet K i t)
          (gammaOddJacobiHeadTransportJet K j t))

theorem finiteVonMangoldtGammaJacobiHeadKreinGram_apply
    (K M N : ℕ) (i j : Fin N) :
    finiteVonMangoldtGammaJacobiHeadKreinGram K M N i j =
      ∑ p : Fin M,
        finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
          (gammaOddJacobiLogHead K (Real.log (((p : ℕ) + 3 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2) -
            gammaOddJacobiLogHead K (Real.log (((p : ℕ) + 2 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2)) := by
  unfold finiteVonMangoldtGammaJacobiHeadKreinGram
  apply Finset.sum_congr rfl
  intro p hp
  rw [intervalIntegral_exchangePair_gammaOddJacobiHeadTransportJet]

/-- At fixed apertures, cofinal odd Jacobi capacity recovers the actual successor current. -/
theorem tendsto_finiteVonMangoldtGammaJacobiHeadKreinGram_apply
    (M N : ℕ) (i j : Fin N) :
    Tendsto (fun K => finiteVonMangoldtGammaJacobiHeadKreinGram K M N i j)
      atTop (nhds (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N i j)) := by
  rw [show (fun K => finiteVonMangoldtGammaJacobiHeadKreinGram K M N i j) =
      fun K => ∑ p : Fin M,
        finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
          (gammaOddJacobiLogHead K (Real.log (((p : ℕ) + 3 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2) -
            gammaOddJacobiLogHead K (Real.log (((p : ℕ) + 2 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2)) by
    funext K
    exact finiteVonMangoldtGammaJacobiHeadKreinGram_apply K M N i j]
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
    finiteVonMangoldtSuccessorRelativeMoment]
  apply tendsto_finsetSum Finset.univ
  intro p hp
  have hs := (tendsto_gammaOddJacobiLogHead
    (Real.log (((p : ℕ) + 3 : ℕ) : ℝ))).pow ((i : ℕ) + (j : ℕ) + 2)
  have ht := (tendsto_gammaOddJacobiLogHead
    (Real.log (((p : ℕ) + 2 : ℕ) : ℝ))).pow ((i : ℕ) + (j : ℕ) + 2)
  have h := (hs.sub ht).const_mul (finiteVonMangoldtRealWeight ((p : ℕ) + 2))
  convert h using 1
  unfold vonMangoldtSuccessorRelativeMomentTerm
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  push_cast
  ring

/-- Whole fixed-aperture matrices converge in their finite-dimensional topology. -/
theorem tendsto_finiteVonMangoldtGammaJacobiHeadKreinGram
    (M N : ℕ) :
    Tendsto (fun K => finiteVonMangoldtGammaJacobiHeadKreinGram K M N)
      atTop (nhds (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finiteVonMangoldtGammaJacobiHeadKreinGram_apply M N i j

/-! ### Adaptive head/tail compatibility -/

/-- Coordinatewise head complementary to the existing zero-padded coherent residual. -/
def gammaOddJacobiPrimeCoherentHeadFeature
    (p : Nat.Primes) (k : ℕ) : ℝ :=
  if k < gammaOddJacobiPrimeCapacity p then gammaOddJacobiPrimeFeature p k else 0

/-- Existing coherent tail and the new incidence head are an exact split of one absolute mode. -/
theorem gammaOddJacobiPrimeCoherentHeadFeature_add_residual
    (p : Nat.Primes) (k : ℕ) :
    gammaOddJacobiPrimeCoherentHeadFeature p k +
        HTGeometry.adaptiveMercerResidualFeature
          gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p k =
      gammaOddJacobiPrimeFeature p k := by
  unfold gammaOddJacobiPrimeCoherentHeadFeature
  unfold HTGeometry.adaptiveMercerResidualFeature
  split_ifs <;> ring

/-- At the source-selected prime capacity, the log head uses exactly the complement of `SR-38`. -/
theorem gammaOddJacobiLogHead_primeCapacity_eq
    (p : Nat.Primes) :
    gammaOddJacobiLogHead (gammaOddJacobiPrimeCapacity p) (Real.log (p : ℝ)) =
      ∑ k ∈ Finset.range (gammaOddJacobiPrimeCapacity p),
        gammaOddJacobiLogIncidence k *
          gammaOddJacobiPrimeCoherentHeadFeature p k /
            semilocalArchimedeanCharacteristic (Real.log (p : ℝ)) := by
  unfold gammaOddJacobiLogHead gammaOddJacobiPrimeCoherentHeadFeature
  unfold gammaOddJacobiPrimeFeature
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (Finset.mem_range.1 hk)]

/-- Diagonal normalization exposing the log coordinate from the actual Gamma feature at a prime. -/
def gammaOddJacobiLogPrimeNormalization (p : Nat.Primes) : ℝ :=
  (semilocalArchimedeanCharacteristic (Real.log (p : ℝ)))⁻¹

/-- Exact singularity law for the common-coordinate connector. -/
theorem gammaOddJacobiLogPrimeNormalization_sq_eq
    (p : Nat.Primes) :
    gammaOddJacobiLogPrimeNormalization p ^ 2 =
      ((p : ℝ) ^ 2 + 1) / (2 * (p : ℝ)) := by
  rw [gammaOddJacobiLogPrimeNormalization, inv_pow,
    semilocalArchimedeanCharacteristic_log_prime_sq]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  field_simp

/-- The normalization grows at least like the square root of the prime label. -/
theorem gammaOddJacobiLogPrimeNormalization_sq_ge
    (p : Nat.Primes) :
    (p : ℝ) / 2 ≤ gammaOddJacobiLogPrimeNormalization p ^ 2 := by
  rw [gammaOddJacobiLogPrimeNormalization_sq_eq]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2 * p)]
  nlinarith

/-- No bounded diagonal map can perform the common-coordinate normalization on all primes. -/
theorem exists_prime_gammaOddJacobiLogPrimeNormalization_sq_gt
    (B : ℝ) :
    ∃ p : Nat.Primes, B < gammaOddJacobiLogPrimeNormalization p ^ 2 := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (2 * B)
  obtain ⟨p : ℕ, hnp, hp⟩ := Nat.exists_infinite_primes n
  let q : Nat.Primes := ⟨p, hp⟩
  refine ⟨q, lt_of_lt_of_le ?_ (gammaOddJacobiLogPrimeNormalization_sq_ge q)⟩
  have hnpReal : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hnp
  dsimp only [q]
  nlinarith

/-- Edge-dependent Jacobi capacities shifted by one cofinal common depth. -/
def finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram
    (capacity : ℕ → ℕ) (L M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ p : Fin M,
    finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
      (∫ t in Real.log (((p : ℕ) + 2 : ℕ) : ℝ)..
          Real.log (((p : ℕ) + 3 : ℕ) : ℝ),
        HTGeometry.exchangePair
          (gammaOddJacobiHeadTransportJet
            (L + capacity ((p : ℕ) + 2)) i t)
          (gammaOddJacobiHeadTransportJet
            (L + capacity ((p : ℕ) + 2)) j t))

theorem finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram_apply
    (capacity : ℕ → ℕ) (L M N : ℕ) (i j : Fin N) :
    finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram capacity L M N i j =
      ∑ p : Fin M,
        finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
          (gammaOddJacobiLogHead (L + capacity ((p : ℕ) + 2))
                (Real.log (((p : ℕ) + 3 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2) -
            gammaOddJacobiLogHead (L + capacity ((p : ℕ) + 2))
                (Real.log (((p : ℕ) + 2 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2)) := by
  unfold finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram
  apply Finset.sum_congr rfl
  intro p hp
  rw [intervalIntegral_exchangePair_gammaOddJacobiHeadTransportJet]

/-- Arbitrary source-dependent starting capacities recover `SR-40` after common cofinal growth. -/
theorem tendsto_finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram_apply
    (capacity : ℕ → ℕ) (M N : ℕ) (i j : Fin N) :
    Tendsto
      (fun L => finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram capacity L M N i j)
      atTop (nhds (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N i j)) := by
  rw [show (fun L =>
      finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram capacity L M N i j) =
      fun L => ∑ p : Fin M,
        finiteVonMangoldtRealWeight ((p : ℕ) + 2) *
          (gammaOddJacobiLogHead (L + capacity ((p : ℕ) + 2))
                (Real.log (((p : ℕ) + 3 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2) -
            gammaOddJacobiLogHead (L + capacity ((p : ℕ) + 2))
                (Real.log (((p : ℕ) + 2 : ℕ) : ℝ)) ^
              ((i : ℕ) + (j : ℕ) + 2)) by
    funext L
    exact finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram_apply
      capacity L M N i j]
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
    finiteVonMangoldtSuccessorRelativeMoment]
  apply tendsto_finsetSum Finset.univ
  intro p hp
  have hs := ((tendsto_gammaOddJacobiLogHead
    (Real.log (((p : ℕ) + 3 : ℕ) : ℝ))).comp
      (tendsto_add_atTop_nat (capacity ((p : ℕ) + 2)))).pow
        ((i : ℕ) + (j : ℕ) + 2)
  have ht := ((tendsto_gammaOddJacobiLogHead
    (Real.log (((p : ℕ) + 2 : ℕ) : ℝ))).comp
      (tendsto_add_atTop_nat (capacity ((p : ℕ) + 2)))).pow
        ((i : ℕ) + (j : ℕ) + 2)
  have h := (hs.sub ht).const_mul (finiteVonMangoldtRealWeight ((p : ℕ) + 2))
  convert h using 1
  · funext L
    rfl
  · unfold vonMangoldtSuccessorRelativeMomentTerm
    unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
    push_cast
    ring

theorem tendsto_finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram
    (capacity : ℕ → ℕ) (M N : ℕ) :
    Tendsto
      (fun L => finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram capacity L M N)
      atTop (nhds (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finiteVonMangoldtGammaJacobiAdaptiveHeadKreinGram_apply
    capacity M N i j

end

end RHTower
