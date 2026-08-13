import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantPacketBound
import GaloisForLFunctions.RHTower.Sieve.MaynardMellinKernelDefect
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition

/-!
# Pole-annihilating target--reference Perron identity

The low-ordinate giant-factor seam cannot be closed by absolute-value moments: a Dirichlet block
longer than the ordinate scale retains its integral (zeta-pole) mode.  This file keeps the two
physical window widths in one exact Perron identity.  Width normalization makes their common pole
mode identical, so target--reference subtraction removes it before any large-value estimate.

The analytic legality is explicit.  Every window-relevant Heath--Brown packet has uniform finite
support, hence its Dirichlet polynomial times either smooth Mellin kernel is integrable.  No
conditional interchange or unproved continuation premise is hidden in the subtraction.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- A finitely supported Dirichlet series times a smooth Perron kernel is integrable on any
positive vertical line. -/
theorem integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  classical
  have hF0 : complexCoeff F 0 = 0 := by
    rw [complexCoeff_apply]
    by_contra hzero
    have hmem := hF 0 (Complex.ofReal_injective.ne_iff.mp hzero)
    simp at hmem
  let W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * I)
  have hterm : ∀ n : ℕ, Integrable (fun y : ℝ =>
      LSeries.term (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) n * W y) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_def]
    · have hperron := integrable_perron_term_general
        hF0 hN hH hsigma n
      refine hperron.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp only [W]
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv,
        ← Complex.cpow_neg]
      ring
  have hfinite : ∀ u : Finset ℕ, Integrable (fun y : ℝ =>
      ∑ n ∈ u, LSeries.term (complexCoeff F)
        ((sigma : ℂ) + (y : ℝ) * I) n * W y) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert n u hnu ih =>
        have hadd := (hterm n).add ih
        refine hadd.congr (Filter.Eventually.of_forall fun y => ?_)
        simp only [Pi.add_apply, Finset.sum_insert hnu]
  refine (hfinite (Finset.Icc 1 M)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  dsimp only [W]
  rw [LSeries_eq_sum_term_of_support (a := complexCoeff F) (fun n hn =>
    hF n (Complex.ofReal_injective.ne_iff.mp hn))]
  rw [Finset.sum_mul]

/-- **Finite-support Perron formula on every positive line.**  Absolute Dirichlet-series
convergence is unnecessary for a Dirichlet polynomial; finite support allows termwise Mellin
inversion as soon as `sigma > 0`. -/
theorem smul_tsum_mul_smoothWeight_eq_integral_of_upperSupported
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  classical
  have hF0 : complexCoeff F 0 = 0 := by
    rw [complexCoeff_apply]
    by_contra hzero
    have hmem := hF 0 (Complex.ofReal_injective.ne_iff.mp hzero)
    simp at hmem
  let W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * I)
  let f : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) n * W y
  have hterm : ∀ n ∈ Finset.Icc 1 M, Integrable (f n) := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hperron := integrable_perron_term_general hF0 hN hH hsigma n
    refine hperron.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [f, W]
    rw [LSeries.term_of_ne_zero hnpos.ne', div_eq_mul_inv,
      ← Complex.cpow_neg]
    ring
  have hintegral := integral_finsetSum (Finset.Icc 1 M) hterm
  have hright :
      (∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) * W y) =
      ∑ n ∈ Finset.Icc 1 M, ∫ y : ℝ, f n y := by
    calc
      (∫ y : ℝ,
        LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I) * W y) =
          ∫ y : ℝ, ∑ n ∈ Finset.Icc 1 M, f n y := by
            apply integral_congr_ae
            filter_upwards with y
            dsimp only [f]
            rw [LSeries_eq_sum_term_of_support (a := complexCoeff F)
              (fun n hn => hF n (Complex.ofReal_injective.ne_iff.mp hn)),
              Finset.sum_mul]
      _ = ∑ n ∈ Finset.Icc 1 M, ∫ y : ℝ, f n y := hintegral
  have htermIntegral : ∀ n ∈ Finset.Icc 1 M,
      (∫ y : ℝ, f n y) =
        (2 * Real.pi : ℝ) • (complexCoeff F n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    dsimp only [f, W]
    have hperron := integral_perron_term
      (a := complexCoeff F) hN hH hsigma hnpos
    calc
      (∫ y : ℝ, f n y) =
          complexCoeff F n *
            ((2 * Real.pi : ℝ) •
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
        rw [← hperron]
        apply integral_congr_ae
        filter_upwards with y
        dsimp only [f, W]
        rw [LSeries.term_of_ne_zero hnpos.ne', div_eq_mul_inv,
          ← Complex.cpow_neg]
        ring
      _ = (2 * Real.pi : ℝ) • (complexCoeff F n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
        rw [mul_smul_comm]
  rw [hright]
  calc
    (2 * Real.pi : ℝ) • (∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
        (2 * Real.pi : ℝ) • (∑ n ∈ Finset.Icc 1 M, complexCoeff F n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
      congr 1
      rw [tsum_eq_sum (s := Finset.Icc 1 M)]
      intro n hn
      have hzeroComplex : complexCoeff F n = 0 := by
        by_contra hne
        exact hn (hF n (Complex.ofReal_injective.ne_iff.mp hne))
      rw [hzeroComplex, zero_mul]
    _ = ∑ n ∈ Finset.Icc 1 M,
        (2 * Real.pi : ℝ) • (complexCoeff F n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
      rw [Finset.smul_sum]
    _ = ∑ n ∈ Finset.Icc 1 M, ∫ y : ℝ, f n y := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (htermIntegral n hn).symm

/-- On the adjacent physical window, the window-relevant eligible packet is coefficient-exactly
von Mangoldt.  Low-total boxes vanish below the left edge and all other recuts preserve every
coefficient meeting the support. -/
theorem tsum_heathBrownWindowRelevantEligiblePacket_routeTSmoothWindowWeight_eq_vonMangoldt
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hH : 0 < H) (hsupport : N + 2 * H ≤ X) :
    (∑' n : ℕ,
      complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ) := by
  apply tsum_congr
  intro n
  by_cases hnN : (n : ℝ) ≤ N
  · have hplus := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
      (show (n : ℝ) ≤ N + H by linarith)
    have hbase := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hnN
    rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
    simp
  · by_cases hnX : n ≤ X
    · have hnNlt : N < (n : ℝ) := lt_of_not_ge hnN
      have hwindow :=
        heathBrownPerronRelevantEligiblePacket_apply_eq_windowRelevant_of_lt
          L X k T0 t hnNlt
      have hperron := heathBrownEligiblePacket_apply_eq_perronRelevant
        L X k T0 t hnX
      have hlow : complexCoeff (heathBrownLowTotalPacket L X k T0 t) n = 0 := by
        by_contra hne
        have hnle := complexCoeff_heathBrownLowTotalPacket_nonzero_le
          L X k hT0 hscale hne
        linarith
      have hsplit := congrArg
        (fun F : ArithmeticFunction ℝ => complexCoeff F n)
        (heathBrownFiniteCompressedPacket_eq_eligible_add_lowTotal L X k T0 t)
      have hcompressed :
          complexCoeff (heathBrownFiniteCompressedPacket L X k) n =
            ((vonMangoldt n : ℝ) : ℂ) := by
        rw [complexCoeff_apply,
          ← heathBrown_finite_compressed_identity L X k n hnX (hnX.trans_lt hXL)]
      have hwindowC :
          complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t) n =
            complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n := by
        simpa only [complexCoeff_apply] using congrArg Complex.ofReal hwindow
      have hperronC :
          complexCoeff (heathBrownEligiblePacket L X k T0 t) n =
            complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t) n := by
        simpa only [complexCoeff_apply] using congrArg Complex.ofReal hperron
      rw [← hwindowC, ← hperronC]
      have helig : complexCoeff (heathBrownEligiblePacket L X k T0 t) n =
          complexCoeff (heathBrownFiniteCompressedPacket L X k) n := by
        have hsplit' : complexCoeff (heathBrownFiniteCompressedPacket L X k) n =
            complexCoeff (heathBrownEligiblePacket L X k T0 t) n +
              complexCoeff (heathBrownLowTotalPacket L X k T0 t) n := by
          simpa [complexCoeff_apply, ArithmeticFunction.add_apply, ofReal_add] using hsplit
        rw [hlow, add_zero] at hsplit'
        exact hsplit'.symm
      rw [helig, hcompressed]
    · have hXn : (X : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_not_ge hnX
      have hzero : routeTSmoothWindowWeight N H (n : ℝ) = 0 := by
        have hplus := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
          (show N + H + H ≤ (n : ℝ) by linarith)
        have hbase := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
          (show N + H ≤ (n : ℝ) by linarith)
        rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
      rw [hzero]
      simp

/-- Mellin transform is genuinely linear on the adjacent smooth window in its convergence
half-plane. -/
theorem mellin_routeTSmoothWindowWeight_eq_sub
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ)) s -
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s := by
  have hplus : MellinConvergent
      (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ)) s := by
    simpa only [MellinConvergent, smul_eq_mul] using
      integrableOn_mellin_smoothWeight (by linarith : 0 ≤ N + H) hH hs
  have hbase : MellinConvergent
      (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s := by
    simpa only [MellinConvergent, smul_eq_mul] using
      integrableOn_mellin_smoothWeight hN hH hs
  simpa only [routeTSmoothWindowWeight, ofReal_sub] using
    (hasMellin_sub hplus hbase).2

/-- Window-relevant aggregate times one smooth cutoff kernel is integrable. -/
theorem integrable_heathBrownWindowRelevantAggregate_mul_mellin_smoothWeight
    (L X k : ℕ) (T0 t N0 : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hint := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t N0)
    hN hH hsigma
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  change LSeries (complexCoeff
      (heathBrownWindowRelevantEligiblePacket L X k T0 t N0))
        ((sigma : ℂ) + (y : ℝ) * I) * _ =
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
        ((sigma : ℂ) + (y : ℝ) * I) * _
  rw [LSeries_heathBrownWindowRelevantEligiblePacket]

/-- Aggregate times the unnormalized adjacent-window Mellin kernel is integrable. -/
theorem integrable_heathBrownWindowRelevantAggregate_mul_routeTMellin
    (L X k : ℕ) (T0 t N : ℝ) {H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hplus := integrable_heathBrownWindowRelevantAggregate_mul_mellin_smoothWeight
    L X k T0 t N (N := N + H) (H := H) (sigma := sigma)
      (by linarith) hH hsigma
  have hbase := integrable_heathBrownWindowRelevantAggregate_mul_mellin_smoothWeight
    L X k T0 t N (N := N) (H := H) (sigma := sigma) hN hH hsigma
  refine (hplus.sub hbase).congr (Filter.Eventually.of_forall fun y => ?_)
  change
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) -
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) =
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)
  rw [mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
    linarith)]
  ring

/-- Aggregate times the normalized adjacent-window Mellin kernel is integrable. -/
theorem integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    (L X k : ℕ) (T0 t N : ℝ) {H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hint := integrable_heathBrownWindowRelevantAggregate_mul_routeTMellin
    L X k T0 t N hN hH hsigma
  have hscaled := hint.const_mul ((H : ℂ)⁻¹)
  refine hscaled.congr (Filter.Eventually.of_forall fun y => ?_)
  change (H : ℂ)⁻¹ *
      (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)
  rw [routeTNormalizedSmoothWindowMellin]
  ring

/-- Exact one-kernel Perron formula for an adjacent physical window. -/
theorem smul_tsum_vonMangoldt_routeTSmoothWindowWeight_eq_integral
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t N
  let M := 2 ^ (2 * k) * X
  have hF : UpperSupported F M := by
    exact upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t N
  have hplusP := smul_tsum_mul_smoothWeight_eq_integral_of_upperSupported hF
    (N := N + H) (H := H) (sigma := sigma) (by linarith) hH hsigma
  have hbaseP := smul_tsum_mul_smoothWeight_eq_integral_of_upperSupported hF
    (N := N) (H := H) (sigma := sigma) hN hH hsigma
  have hplus := integrable_heathBrownWindowRelevantAggregate_mul_mellin_smoothWeight
    L X k T0 t N (N := N + H) (H := H) (sigma := sigma)
      (by linarith) hH hsigma
  have hbase := integrable_heathBrownWindowRelevantAggregate_mul_mellin_smoothWeight
    L X k T0 t N (N := N) (H := H) (sigma := sigma)
      hN hH hsigma
  have hplusSum : Summable fun n : ℕ => complexCoeff F n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 M) fun n hn => ?_
    have hzero : complexCoeff F n = 0 := by
      by_contra hne
      exact hn (hF n (Complex.ofReal_injective.ne_iff.mp hne))
    rw [hzero, zero_mul]
  have hbaseSum : Summable fun n : ℕ => complexCoeff F n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 M) fun n hn => ?_
    have hzero : complexCoeff F n = 0 := by
      by_contra hne
      exact hn (hF n (Complex.ofReal_injective.ne_iff.mp hne))
    rw [hzero, zero_mul]
  have hpacketAdjacent :
      (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)) -
      ∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hplusSum.tsum_sub hbaseSum]
    apply tsum_congr
    intro n
    rw [routeTSmoothWindowWeight, ofReal_sub, mul_sub]
  have hpacketExact :=
    tsum_heathBrownWindowRelevantEligiblePacket_routeTSmoothWindowWeight_eq_vonMangoldt
      L X k hXL hT0 hscale hH hsupport
  have hperron : (2 * Real.pi : ℝ) •
      (∑' n : ℕ, complexCoeff F n *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    rw [hpacketAdjacent, smul_sub]
    rw [hplusP, hbaseP]
    apply congrArg₂ (· - ·)
    · apply integral_congr_ae
      filter_upwards with y
      rw [LSeries_heathBrownWindowRelevantEligiblePacket]
    · apply integral_congr_ae
      filter_upwards with y
      rw [LSeries_heathBrownWindowRelevantEligiblePacket]
  rw [← integral_sub hplus hbase] at hperron
  calc
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
        (2 * Real.pi : ℝ) • (∑' n : ℕ, complexCoeff F n *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) := by
            apply congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z)
            exact hpacketExact.symm
    _ = ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
              ((sigma : ℂ) + (y : ℝ) * I) := by
      rw [hperron]
      apply integral_congr_ae
      filter_upwards with y
      rw [mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
        linarith)]
      ring

/-- Width-normalized adjacent von Mangoldt mass has exact Perron kernel
`routeTNormalizedSmoothWindowMellin`. -/
theorem smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I) := by
  have hraw := smul_tsum_vonMangoldt_routeTSmoothWindowWeight_eq_integral
    L X k hXL hT0 hscale hN hH hsupport hsigma
  calc
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
        (H : ℂ)⁻¹ * ((2 * Real.pi : ℝ) •
          (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) := by
              exact (mul_smul_comm (2 * Real.pi : ℝ) (H : ℂ)⁻¹
                (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
                  ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))).symm
    _ = (H : ℂ)⁻¹ * ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
              ((sigma : ℂ) + (y : ℝ) * I) := by rw [hraw]
    _ = ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [routeTNormalizedSmoothWindowMellin]
      ring

/-- **Exact pole-annihilating target--reference Perron identity.**  Both physical widths use the
same window-relevant arithmetic aggregate; their difference is entirely in a normalized Mellin
kernel that vanishes at `s = 1`. -/
theorem smul_normalized_reference_sub_target_vonMangoldt_eq_integral_kernelDefect
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma) :
    (2 * Real.pi : ℝ) •
        ((R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
          (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I)) := by
  have href :=
    smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral
      L X k hXL hT0 hscale hN hR hsupportR hsigma
  have htarget :=
    smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral
      L X k hXL hT0 hscale hN hH hsupportH hsigma
  have hintR :=
    integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hR hsigma
  have hintH :=
    integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hH hsigma
  calc
    (2 * Real.pi : ℝ) •
        ((R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
          (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
        (2 * Real.pi : ℝ) •
            ((R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ))) -
          (2 * Real.pi : ℝ) •
            ((H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) := by
                rw [smul_sub]
    _ = (∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I)) -
        ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I) := by rw [href, htarget]
    _ = ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I) :=
      (integral_sub hintR hintH).symm
    _ = ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((sigma : ℂ) + (y : ℝ) * I)) := by
      apply integral_congr_ae
      filter_upwards with y
      ring

/-- The exact kernel in the target--reference Perron identity annihilates the zeta pole. -/
theorem normalized_reference_sub_target_PerronKernel_one
    {N H R : ℝ} (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) :
    routeTNormalizedSmoothWindowMellin N R 1 -
        routeTNormalizedSmoothWindowMellin N H 1 = 0 :=
  routeT_normalized_reference_target_pole_cancel hN.le hH hR

/-- On the common low-frequency band, the exact Perron integrand contains only the quantitative
kernel defect; the unresolved common pole mode has disappeared. -/
theorem norm_windowRelevantAggregate_mul_normalizedKernelDefect_le
    (L X k : ℕ) (T0 t N : ℝ) {H R : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    {s : ℂ} (hs : 0 < s.re)
    (hsmallR : ‖s - 1‖ * (2 * R / N) ≤ 1) :
    ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s *
        (routeTNormalizedSmoothWindowMellin N R s -
          routeTNormalizedSmoothWindowMellin N H s)‖ ≤
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s‖ *
        (8 * N ^ (s.re - 1) * ‖s - 1‖ * (R / N)) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR hs hsmallR)
    (norm_nonneg _)

/-- **Low-frequency pole-defect bound.**  On a symmetric ordinate interval contained in the
common Mellin band, a uniform aggregate bound pays an extra factor
`(R/N)(|sigma-1|+U)`.  This is the quantitative gain unavailable before pole cancellation. -/
theorem norm_intervalIntegral_windowRelevantAggregate_mul_normalizedKernelDefect_le
    (L X k : ℕ) (T0 t N : ℝ) {H R sigma U B : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsigma : 0 < sigma) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hsmall : (|sigma - 1| + U) * (2 * R / N) ≤ 1)
    (haggregate : ∀ y ∈ Set.uIoc (-U) U,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤ B) :
    ‖∫ y in (-U)..U,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖ ≤
      (B * (8 * N ^ (sigma - 1) * (|sigma - 1| + U) * (R / N))) * (2 * U) := by
  have hpoint : ∀ y ∈ Set.uIoc (-U) U,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖ ≤
      B * (8 * N ^ (sigma - 1) * (|sigma - 1| + U) * (R / N)) := by
    intro y hy
    have hyIoc : y ∈ Set.Ioc (-U) U := by
      simpa [Set.uIoc_of_le (by linarith : -U ≤ U)] using hy
    have hyabs : |y| ≤ U := abs_le.mpr ⟨hyIoc.1.le, hyIoc.2⟩
    let s : ℂ := (sigma : ℂ) + (y : ℝ) * I
    have hsre : 0 < s.re := by
      simpa [s] using hsigma
    have hsnorm : ‖s - 1‖ ≤ |sigma - 1| + U := by
      calc
        ‖s - 1‖ = ‖((sigma - 1 : ℝ) : ℂ) + (y : ℝ) * I‖ := by
          dsimp only [s]
          congr 1
          push_cast
          ring
        _ ≤ ‖((sigma - 1 : ℝ) : ℂ)‖ + ‖(y : ℝ) * I‖ := norm_add_le _ _
        _ = |sigma - 1| + |y| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, norm_I, mul_one]
        _ ≤ |sigma - 1| + U := add_le_add (le_refl |sigma - 1|) hyabs
    have hsmallY : ‖s - 1‖ * (2 * R / N) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsnorm (by positivity : 0 ≤ 2 * R / N)).trans hsmall
    have hkernel := norm_windowRelevantAggregate_mul_normalizedKernelDefect_le
      L X k T0 t N hN hH hR hHR hsre hsmallY
    dsimp only [s] at hkernel
    have hsreEq : ((sigma : ℂ) + (y : ℝ) * I).re = sigma := by simp
    rw [hsreEq] at hkernel
    change ‖((sigma : ℂ) + (y : ℝ) * I) - 1‖ ≤ |sigma - 1| + U at hsnorm
    calc
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖ ≤
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I)‖ *
              (8 * N ^ (sigma - 1) * ‖s - 1‖ * (R / N)) := hkernel
      _ ≤ B * (8 * N ^ (sigma - 1) * (|sigma - 1| + U) * (R / N)) := by
        have hkernelFactor :
            8 * N ^ (sigma - 1) *
                ‖((sigma : ℂ) + (y : ℝ) * I) - 1‖ * (R / N) ≤
              8 * N ^ (sigma - 1) * (|sigma - 1| + U) * (R / N) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsnorm (by positivity)) (by positivity)
        exact mul_le_mul (haggregate y hy) hkernelFactor (by positivity) hB
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (by linarith : 0 ≤ U - -U)] at hinterval
  convert hinterval using 1 <;> ring

/-- **Closed low-frequency estimate.**  Fixed divisor moments remove the pointwise
`N^epsilon` loss, so the pole defect is multiplied only by an explicit fixed polylogarithmic
packet envelope. -/
theorem norm_intervalIntegral_windowRelevantAggregate_mul_normalizedKernelDefect_le_fixedPolylog
    (L X k : ℕ) (hX : 1 ≤ X) (T0 t N H R sigma U : ℝ)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsigma : 0 < sigma) (hU : 0 ≤ U)
    (hsmall : (|sigma - 1| + U) * (2 * R / N) ≤ 1) :
    ‖∫ y in (-U)..U,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖ ≤
      (heathBrownWindowRelevantFixedPolylogBound L X k N sigma *
        (8 * N ^ (sigma - 1) * (|sigma - 1| + U) * (R / N))) *
          (2 * U) := by
  let M : ℕ := 2 ^ (2 * k) * X
  have hM : 1 ≤ M := by
    dsimp only [M]
    simpa only [one_mul] using
      Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hB : 0 ≤ heathBrownWindowRelevantFixedPolylogBound L X k N sigma := by
    dsimp only [heathBrownWindowRelevantFixedPolylogBound, M] at hlog ⊢
    positivity
  apply norm_intervalIntegral_windowRelevantAggregate_mul_normalizedKernelDefect_le
    L X k T0 t N (H := H) (R := R) (sigma := sigma) (U := U)
      (B := heathBrownWindowRelevantFixedPolylogBound L X k N sigma)
      hN hH hR hHR hsigma hU hB hsmall
  intro y _hy
  exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
    L X k hX T0 t N sigma y hN hsigma.le

/-- A wide reference mass and a prime-free target force a fixed normalized physical discrepancy
once local prime-power leakage is below one quarter of the reference margin. -/
theorem norm_normalized_reference_sub_primeFree_target_vonMangoldt_ge
    {N H R : ℝ} (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R)
    (hwidthH : 1 ≤ 2 * H)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (R / 2) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin / 4) :
    routeTSmoothWindowCentralMargin / 4 ≤
      ‖(R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
        (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))‖ := by
  let MR : ℝ := ∑' n : ℕ,
    (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n
  let MH : ℝ := ∑' n : ℕ,
    (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n
  let E : ℝ := (Real.log (N + 2 * H) / Real.log 2) *
    (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H)
  have htarget : MH ≤ E := by
    dsimp only [MH, E]
    exact routeT_primeFree_smooth_vonMangoldt_mass_le_local_primePower
      hN hH hwidthH hprimeFree
  have hrefNorm : routeTSmoothWindowCentralMargin / 2 ≤ MR / R := by
    rw [le_div_iff₀ hR]
    calc
      routeTSmoothWindowCentralMargin / 2 * R =
          routeTSmoothWindowCentralMargin * (R / 2) := by ring
      _ ≤ MR := href
  have htargetNorm : MH / H ≤ routeTSmoothWindowCentralMargin / 4 := by
    calc
      MH / H ≤ E / H := div_le_div_of_nonneg_right htarget hH.le
      _ ≤ routeTSmoothWindowCentralMargin / 4 := by simpa only [E] using hleakage
  have hgap : routeTSmoothWindowCentralMargin / 4 ≤ MR / R - MH / H := by
    linarith
  have hcomplexR :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) = (MR : ℂ) := by
    calc
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) =
          ∑' n : ℕ, (((vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N R n : ℝ) : ℂ) := by
              apply tsum_congr
              intro n
              rw [ofReal_mul]
      _ = (MR : ℂ) := by
        dsimp only [MR]
        exact (Complex.ofReal_tsum _).symm
  have hcomplexH :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) = (MH : ℂ) := by
    calc
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
          ∑' n : ℕ, (((vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N H n : ℝ) : ℂ) := by
              apply tsum_congr
              intro n
              rw [ofReal_mul]
      _ = (MH : ℂ) := by
        dsimp only [MH]
        exact (Complex.ofReal_tsum _).symm
  rw [hcomplexR, hcomplexH]
  have hcast : (R : ℂ)⁻¹ * (MR : ℂ) - (H : ℂ)⁻¹ * (MH : ℂ) =
      ((MR / R - MH / H : ℝ) : ℂ) := by
    push_cast
    field_simp [hR.ne', hH.ne']
  have hgap0 : 0 ≤ MR / R - MH / H :=
    (div_nonneg routeTSmoothWindowCentralMargin_pos.le (by norm_num)).trans hgap
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hgap0]
  exact hgap

/-- **Large signed Perron-error producer.**  Under prime-freeness, reference calibration and local
prime-power control force the pole-annihilating vertical integral to have fixed positive norm.
This is the exact analytic event to which the Route-T `L²` count receiver must be applied. -/
theorem norm_integral_normalizedKernelDefect_ge_of_primeFree
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R)
    (hwidthH : 1 ≤ 2 * H)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (R / 2) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin / 4) :
    (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4) ≤
      ‖∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  let Z : ℂ :=
    (R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
      (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))
  let J : ℂ := ∫ y : ℝ,
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((sigma : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I))
  have hgap : routeTSmoothWindowCentralMargin / 4 ≤ ‖Z‖ := by
    dsimp only [Z]
    exact norm_normalized_reference_sub_primeFree_target_vonMangoldt_ge
      hN hH hR hwidthH hprimeFree href hleakage
  have hidentity : (2 * Real.pi : ℝ) • Z = J := by
    dsimp only [Z, J]
    exact smul_normalized_reference_sub_target_vonMangoldt_eq_integral_kernelDefect
      L X k hXL hT0 hscale (by linarith) hH hR
        hsupportH hsupportR hsigma
  calc
    (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4) ≤
        (2 * Real.pi) * ‖Z‖ :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = ‖(2 * Real.pi : ℝ) • Z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    _ = ‖J‖ := congrArg norm hidentity

end RHTower.Sieve
