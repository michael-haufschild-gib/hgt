import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette
import GaloisForLFunctions.HTGeometry.GammaJetProjectiveBoundary
import GaloisForLFunctions.HTGeometry.PolygammaShift
import GaloisForLFunctions.HTGeometry.QuantitativeHolderInterface

/-!
# Polynomial sector bounds for half-argument digamma jets

This module supplies the growth input for Watson uniqueness.  The shifted variable `z` is
restricted to the closed sector

`-‖z‖ / 2 ≤ re z`,

which contains `|arg z| ≤ 2π/3`.  On this sector every denominator
`(1 + z) / 2 + n` stays a fixed fraction of `‖z‖ + n + 1` away from zero.  Gauss's series and the
all-order polygamma shift formula then give a linear bound for every digamma jet.  A finite
multivariate polynomial in those jets consequently has polynomial growth.
-/

noncomputable section

open Complex Filter Finset MvPolynomial
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

/-- The closed `2π/3` sector in an argument-free form. -/
def digammaWatsonSector : Set ℂ := {z | -(‖z‖ / 2) ≤ z.re}

theorem norm_add_of_mem_digammaWatsonSector {z : ℂ} (hz : z ∈ digammaWatsonSector)
    {t : ℝ} (ht : 0 ≤ t) :
    (‖z‖ + t) / 2 ≤ ‖z + (t : ℂ)‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  have hzsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  change -(‖z‖ / 2) ≤ z.re at hz
  nlinarith [sq_nonneg (‖z‖ - t)]

/-- Uniform denominator separation for the shifted half-argument digamma poles. -/
theorem norm_halfShift_add_nat_lower {z : ℂ} (hz : z ∈ digammaWatsonSector) (n : ℕ) :
    (‖z‖ + (2 * (n : ℝ) + 1)) / 4 ≤ ‖(1 + z) / 2 + (n : ℂ)‖ := by
  have h := norm_add_of_mem_digammaWatsonSector hz
    (t := 2 * (n : ℝ) + 1) (by positivity)
  have heq : (1 + z) / 2 + (n : ℂ) = (z + ((2 * (n : ℝ) + 1 : ℝ) : ℂ)) / 2 := by
    push_cast
    ring
  rw [heq, norm_div]
  norm_num only [norm_ofNat]
  calc
    (‖z‖ + (2 * (n : ℝ) + 1)) / 4 =
        ((‖z‖ + (2 * (n : ℝ) + 1)) / 2) / 2 := by ring
    _ ≤ ‖z + ((2 * (n : ℝ) + 1 : ℝ) : ℂ)‖ / 2 :=
      div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

theorem halfShift_ne_neg_nat {z : ℂ} (hz : z ∈ digammaWatsonSector) (n : ℕ) :
    (1 + z) / 2 ≠ -(n : ℂ) := by
  intro hzero
  have hnorm : ‖(1 + z) / 2 + (n : ℂ)‖ = 0 := by rw [hzero]; simp
  have hlower := norm_halfShift_add_nat_lower hz n
  rw [hnorm] at hlower
  have hpos : 0 < (‖z‖ + (2 * (n : ℝ) + 1)) / 4 := by positivity
  linarith

private theorem summable_one_div_nat_add_one_pow (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ q) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (q : ℝ)).2 (by exact_mod_cast hq)
  apply h.congr
  intro n
  rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), Real.rpow_natCast]

private theorem gaussDigammaSeriesTerm_eq_of_offPoles
    {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) (n : ℕ) :
    RHTower.gaussDigammaSeriesTerm s n =
      (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hsn : s + (n : ℂ) ≠ 0 := by
    intro hzero
    apply hs n
    linear_combination hzero
  unfold RHTower.gaussDigammaSeriesTerm
  field_simp [hn1, hsn]
  ring

private theorem norm_gaussDigammaSeriesTerm_halfShift_le {z : ℂ}
    (hz : z ∈ digammaWatsonSector) (n : ℕ) :
    ‖RHTower.gaussDigammaSeriesTerm ((1 + z) / 2) n‖ ≤
      2 * (1 + ‖z‖) * (1 / ((n : ℝ) + 1) ^ 2) := by
  rw [gaussDigammaSeriesTerm_eq_of_offPoles (fun k => halfShift_ne_neg_nat hz k),
    norm_div, norm_mul]
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hnnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  rw [hnnorm]
  rw [div_mul_eq_div_div]
  have hnum : ‖(1 + z) / 2 - 1‖ ≤ (1 + ‖z‖) / 2 := by
    rw [show (1 + z) / 2 - 1 = (z - 1) / 2 by ring, norm_div]
    norm_num
    have := norm_sub_le z 1
    simpa [add_comm] using (div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2))
  have hden := norm_halfShift_add_nat_lower hz n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden' : ((n : ℝ) + 1) / 4 ≤ ‖(1 + z) / 2 + (n : ℂ)‖ := by
    linarith [norm_nonneg z]
  have hdenpos : 0 < ‖(1 + z) / 2 + (n : ℂ)‖ :=
    lt_of_lt_of_le (by positivity : 0 < ((n : ℝ) + 1) / 4) hden'
  calc
    ‖(1 + z) / 2 - 1‖ /
          ((n : ℝ) + 1) / ‖(1 + z) / 2 + (n : ℂ)‖
        ≤ ((1 + ‖z‖) / 2) /
          ((n : ℝ) + 1) / ‖(1 + z) / 2 + (n : ℂ)‖ := by
            gcongr
    _ ≤ ((1 + ‖z‖) / 2) / ((n : ℝ) + 1) / (((n : ℝ) + 1) / 4) := by
            gcongr
    _ = 2 * (1 + ‖z‖) * (1 / ((n : ℝ) + 1) ^ 2) := by
            field_simp
            ring

/-- Digamma has at most linear growth on the shifted Watson sector. -/
theorem exists_norm_digamma_halfShift_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ digammaWatsonSector,
      ‖Complex.digamma ((1 + z) / 2)‖ ≤ C * (1 + ‖z‖) := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have ha : Summable a := summable_one_div_nat_add_one_pow 2 (by omega)
  let A : ℝ := ∑' n, a n
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  let C : ℝ := 2 * A + |Real.eulerMascheroniConstant|
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hz
  let s : ℂ := (1 + z) / 2
  have hoff : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n => halfShift_ne_neg_nat hz n
  have habs : Summable (fun n : ℕ => ‖RHTower.gaussDigammaSeriesTerm s n‖) :=
    GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all s
  have hmajor : Summable (fun n : ℕ => 2 * (1 + ‖z‖) * a n) :=
    ha.mul_left (2 * (1 + ‖z‖))
  have htsum :
      (∑' n : ℕ, ‖RHTower.gaussDigammaSeriesTerm s n‖) ≤
        2 * (1 + ‖z‖) * A := by
    calc
      (∑' n : ℕ, ‖RHTower.gaussDigammaSeriesTerm s n‖)
          ≤ ∑' n : ℕ, 2 * (1 + ‖z‖) * a n :=
        Summable.tsum_le_tsum
          (fun n => norm_gaussDigammaSeriesTerm_halfShift_le hz n) habs hmajor
      _ = 2 * (1 + ‖z‖) * A := by rw [tsum_mul_left]
  have hseries :=
    GaloisForLFunctions.HTGeometry.tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles
      s hoff
  have hpsi : Complex.digamma s =
      (∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s n) -
        (Real.eulerMascheroniConstant : ℂ) := by
    rw [hseries]
    ring
  rw [hpsi]
  calc
    ‖(∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s n) -
          (Real.eulerMascheroniConstant : ℂ)‖
        ≤ ‖∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s n‖ +
            ‖(Real.eulerMascheroniConstant : ℂ)‖ := norm_sub_le _ _
    _ ≤ (∑' n : ℕ, ‖RHTower.gaussDigammaSeriesTerm s n‖) +
            |Real.eulerMascheroniConstant| := by
          gcongr
          · exact norm_tsum_le_tsum_norm habs
          · simp
    _ ≤ 2 * (1 + ‖z‖) * A + |Real.eulerMascheroniConstant| := by gcongr
    _ ≤ C * (1 + ‖z‖) := by
      dsimp [C]
      nlinarith [norm_nonneg z, abs_nonneg Real.eulerMascheroniConstant]

private def polygammaSectorTerm (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) * ((m + 1).factorial : ℂ) / (s + n) ^ (m + 2)

private theorem norm_polygammaSectorTerm_halfShift_le (m : ℕ) {z : ℂ}
    (hz : z ∈ digammaWatsonSector) (n : ℕ) :
    ‖polygammaSectorTerm m ((1 + z) / 2) n‖ ≤
      ((m + 1).factorial : ℝ) * 4 ^ (m + 2) *
        (1 / ((n : ℝ) + 1) ^ (m + 2)) := by
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hden := norm_halfShift_add_nat_lower hz n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden' : ((n : ℝ) + 1) / 4 ≤ ‖(1 + z) / 2 + (n : ℂ)‖ := by
    linarith [norm_nonneg z]
  have hpow : (((n : ℝ) + 1) / 4) ^ (m + 2) ≤
      ‖(1 + z) / 2 + (n : ℂ)‖ ^ (m + 2) :=
    pow_le_pow_left₀ (by positivity) hden' _
  have hnormpos : 0 < ‖(1 + z) / 2 + (n : ℂ)‖ :=
    lt_of_lt_of_le (by positivity : 0 < ((n : ℝ) + 1) / 4) hden'
  have hdenpos : 0 < ‖(1 + z) / 2 + (n : ℂ)‖ ^ (m + 2) :=
    pow_pos hnormpos _
  have hfacnorm : ‖(((m + 1).factorial : ℕ) : ℂ)‖ = ((m + 1).factorial : ℝ) := by
    rw [show (((m + 1).factorial : ℕ) : ℂ) =
      ((((m + 1).factorial : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [polygammaSectorTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, hfacnorm, norm_pow]
  calc
    ((m + 1).factorial : ℝ) /
          ‖(1 + z) / 2 + (n : ℂ)‖ ^ (m + 2)
        ≤ ((m + 1).factorial : ℝ) / (((n : ℝ) + 1) / 4) ^ (m + 2) := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
              (by positivity) hpow
    _ = ((m + 1).factorial : ℝ) * 4 ^ (m + 2) *
          (1 / ((n : ℝ) + 1) ^ (m + 2)) := by
            rw [div_pow]
            field_simp

private theorem tsum_polygammaSectorTerm_eq (m : ℕ) {z : ℂ}
    (hz : z ∈ digammaWatsonSector) :
    (∑' n : ℕ, polygammaSectorTerm m ((1 + z) / 2) n) =
      -iteratedDeriv (m + 1) Complex.digamma ((1 + z) / 2) := by
  let s : ℂ := (1 + z) / 2
  let K : ℝ := ((m + 1).factorial : ℝ) * 4 ^ (m + 2)
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ (m + 2)
  have ha : Summable a := summable_one_div_nat_add_one_pow (m + 2) (by omega)
  have hnorm : Summable (fun n : ℕ => ‖polygammaSectorTerm m s n‖) := by
    apply (ha.mul_left K).of_nonneg_of_le
    · exact fun n => norm_nonneg _
    · exact fun n => norm_polygammaSectorTerm_halfShift_le m hz n
  have hsum : Summable (polygammaSectorTerm m s) := hnorm.of_norm
  have hpartial : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, polygammaSectorTerm m s n) =
        iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ)) -
          iteratedDeriv (m + 1) Complex.digamma s := by
    intro N
    have hshift := HTGeometry.iteratedDeriv_digamma_add_nat (m + 1) s
      (fun n => halfShift_ne_neg_nat hz n) N
    change iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ)) =
      iteratedDeriv (m + 1) Complex.digamma s +
        ∑ n ∈ Finset.range N, polygammaSectorTerm m s n at hshift
    calc
      (∑ n ∈ Finset.range N, polygammaSectorTerm m s n) =
          (iteratedDeriv (m + 1) Complex.digamma s +
            ∑ n ∈ Finset.range N, polygammaSectorTerm m s n) -
              iteratedDeriv (m + 1) Complex.digamma s := by ring
      _ = iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ)) -
          iteratedDeriv (m + 1) Complex.digamma s := by rw [← hshift]
  have hfar := GaloisForLFunctions.iteratedDeriv_digamma_add_nat_tendsto m s
  have hright : Tendsto
      (fun N : ℕ => iteratedDeriv (m + 1) Complex.digamma (s + (N : ℂ)) -
        iteratedDeriv (m + 1) Complex.digamma s)
      atTop (nhds (0 - iteratedDeriv (m + 1) Complex.digamma s)) :=
    hfar.sub tendsto_const_nhds
  have heq : (∑' n : ℕ, polygammaSectorTerm m s n) =
      0 - iteratedDeriv (m + 1) Complex.digamma s := by
    apply tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat
    exact hright.congr (fun N => (hpartial N).symm)
  simpa [s] using heq

/-- Every positive-order polygamma is uniformly bounded on the shifted Watson sector. -/
theorem exists_norm_iteratedDeriv_succ_digamma_halfShift_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ digammaWatsonSector,
      ‖iteratedDeriv (m + 1) Complex.digamma ((1 + z) / 2)‖ ≤ C := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ (m + 2)
  have ha : Summable a := summable_one_div_nat_add_one_pow (m + 2) (by omega)
  let A : ℝ := ∑' n, a n
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  let C : ℝ := ((m + 1).factorial : ℝ) * 4 ^ (m + 2) * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hz
  let s : ℂ := (1 + z) / 2
  let K : ℝ := ((m + 1).factorial : ℝ) * 4 ^ (m + 2)
  have hnorm : Summable (fun n : ℕ => ‖polygammaSectorTerm m s n‖) := by
    apply (ha.mul_left K).of_nonneg_of_le
    · exact fun n => norm_nonneg _
    · exact fun n => norm_polygammaSectorTerm_halfShift_le m hz n
  have hmajor : Summable (fun n : ℕ => K * a n) := ha.mul_left K
  have htsum : (∑' n : ℕ, ‖polygammaSectorTerm m s n‖) ≤ K * A := by
    calc
      (∑' n : ℕ, ‖polygammaSectorTerm m s n‖) ≤ ∑' n : ℕ, K * a n :=
        Summable.tsum_le_tsum
          (fun n => norm_polygammaSectorTerm_halfShift_le m hz n) hnorm hmajor
      _ = K * A := by rw [tsum_mul_left]
  have hseries := tsum_polygammaSectorTerm_eq m hz
  rw [← norm_neg, ← hseries]
  exact (norm_tsum_le_tsum_norm hnorm).trans (by simpa [C, K, A] using htsum)

theorem exists_norm_iteratedDeriv_digamma_halfShift_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ digammaWatsonSector,
      ‖iteratedDeriv j Complex.digamma ((1 + z) / 2)‖ ≤ C * (1 + ‖z‖) := by
  cases j with
  | zero =>
      simpa using exists_norm_digamma_halfShift_le
  | succ m =>
      obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedDeriv_succ_digamma_halfShift_le m
      refine ⟨C, hC, ?_⟩
      intro z hz
      exact (hbound z hz).trans (by
        have hfac : 1 ≤ 1 + ‖z‖ := by nlinarith [norm_nonneg z]
        simpa using mul_le_mul_of_nonneg_left hfac hC)

/-- A differential polynomial in the shifted half-argument digamma jets has polynomial growth on
the closed Watson sector. -/
theorem exists_halfDigammaJetEval_one_add_norm_le (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ digammaWatsonSector,
      ‖halfDigammaJetEval n P (1 + z)‖ ≤ C * (1 + ‖z‖) ^ P.totalDegree := by
  have hj : ∀ j : Fin (n + 1),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ digammaWatsonSector,
        ‖iteratedDeriv (j : ℕ) Complex.digamma ((1 + z) / 2)‖ ≤ C * (1 + ‖z‖) :=
    fun j => exists_norm_iteratedDeriv_digamma_halfShift_le (j : ℕ)
  choose Cj hCj hjet using hj
  let B : ℝ := 1 + ∑ j : Fin (n + 1), Cj j
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hCj j)
  let C : ℝ := (∑ d ∈ P.support, ‖MvPolynomial.coeff d P‖) * B ^ P.totalDegree
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z hz
  let v : Fin (n + 2) → ℂ := Fin.cons (1 + z) fun j : Fin (n + 1) =>
    iteratedDeriv (j : ℕ) Complex.digamma ((1 + z) / 2)
  have hbase : 1 ≤ B * (1 + ‖z‖) := by
    nlinarith [norm_nonneg z]
  have hv : ∀ i : Fin (n + 2), ‖v i‖ ≤ B * (1 + ‖z‖) := by
    intro i
    induction i using Fin.cases with
    | zero =>
        simp only [v, Fin.cons_zero]
        refine (norm_add_le 1 z).trans ?_
        norm_num
        nlinarith [norm_nonneg z]
    | succ j =>
        simp only [v, Fin.cons_succ]
        refine (hjet j z hz).trans ?_
        have hjB : Cj j ≤ B := by
          have hle : Cj j ≤ ∑ k : Fin (n + 1), Cj k :=
            Finset.single_le_sum (fun k _ => hCj k) (Finset.mem_univ j)
          dsimp [B]
          linarith
        exact mul_le_mul_of_nonneg_right hjB (by positivity)
  have heval := GaloisForLFunctions.norm_eval_le_pow P v (B * (1 + ‖z‖)) hbase hv
  change ‖MvPolynomial.eval v P‖ ≤ C * (1 + ‖z‖) ^ P.totalDegree
  refine heval.trans_eq ?_
  dsimp [C]
  rw [mul_pow]
  ring

theorem analyticAt_halfDigammaJetEval_one_add (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ} (hz : z ∈ digammaWatsonSector) :
    AnalyticAt ℂ (fun w => halfDigammaJetEval n P (1 + w)) z := by
  have houter := GaloisForLFunctions.analyticAt_halfDigammaJetEval n P
    (z := 1 + z) (fun p => halfShift_ne_neg_nat hz p)
  have hcomp := AnalyticAt.comp (f := fun w : ℂ => 1 + w) (x := z) houter
    (analyticAt_const.add analyticAt_id)
  simpa [Function.comp] using hcomp

end GaloisForLFunctions.HTGeometry

end
