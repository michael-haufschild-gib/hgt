import GaloisForLFunctions.HTGeometry.TopSymbolWimanPlace
import GaloisForLFunctions.HTGeometry.FirstOrderWimanSlope

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Every transcendental entire order-one ADE admits one canonical positive-derivative top relation
and one escaping Wiman--Valiron subsequence on which its top symbol vanishes, its relative
logarithmic-derivative defect vanishes, and its central-index log slope converges to a strictly
positive finite number. -/
theorem exists_firstOrderWimanTopRelationSlope_of_relation
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0)
    (hPrel : ∀ w : ℂ, MvPolynomial.eval
      (Fin.cons w fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) w) P = 0) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d m : ℕ)
        (y : ℕ → ℝ) (z : ℕ → ℂ) (q : ℝ),
      (∀ p ∈ S, p.1 + p.2 ≤ d) ∧
      (∀ w : ℂ,
        ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 *
          (deriv (coeffFun a) w) ^ p.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      0 < q ∧ Tendsto (fun n => Real.exp (y n)) atTop atTop ∧
      (∀ n, ‖z n‖ = Real.exp (y n)) ∧
      (∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ)) ∧
      Tendsto (fun n => Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n)
        atTop (nhds q) ∧
      Tendsto (fun n =>
        ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
          (A p).eval (z n) * (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ p.2‖)
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        ‖z n * deriv (coeffFun a) (z n) / coeffFun a (z n) -
          (centralIndex a (Real.exp (y n)) : ℂ)‖ /
            (centralIndex a (Real.exp (y n)) : ℝ)) atTop (nhds 0) ∧
      firstOrderMvPoly S A =
        MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
      IsPositiveDerivativeCoefficientShift P S A d := by
  classical
  let hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1 :=
    ⟨P, hP, hPrel⟩
  obtain ⟨S, A, d, m, hdeg, hrel, hmpos, hmle, htarget, htopdeg, hAne, hAdeg,
    hpoly, hshift⟩ :=
    exists_firstOrderPositiveDerivativeTopRelation_of_relation P hP hPrel
  obtain ⟨d₀, C₀, hC₀, hlower⟩ :=
    exists_radius_le_centralIndex_pow_of_order_one ha hn₀ htrans hDA
  obtain ⟨C₁, K, hC₁, hupper⟩ :=
    exists_centralIndex_le_pow_of_order_one ha hn₀ htrans hDA
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  choose M hM using fun n : ℕ =>
    exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel (hδpos n) (hδpos n)
  choose r hrlarge hrlower using fun n : ℕ =>
    hlower (Real.exp (max (M n) ((n : ℝ) + 2)))
  have hrpos : ∀ n, 0 < r n := by
    intro n
    exact lt_of_lt_of_le (Real.exp_pos _) (hrlarge n)
  have hlogrlarge : ∀ n, max (M n) ((n : ℝ) + 2) ≤ Real.log (r n) := by
    intro n
    rw [← Real.exp_le_exp, Real.exp_log (hrpos n)]
    exact hrlarge n
  choose y hylo hyhi z hz htop hdefect using fun n : ℕ => hM n (Real.log (r n))
  have hyhi' : ∀ n,
      y n ≤ Real.log (r n) + Nevanlinna.borelWindow (1 / 4) + 1 := by
    intro n
    have hMle : M n ≤ Real.log (r n) :=
      le_trans (le_max_left _ _) (hlogrlarge n)
    simpa [max_eq_left hMle] using hyhi n
  have hyn2 : ∀ n : ℕ, (n : ℝ) + 2 ≤ y n := by
    intro n
    calc
      (n : ℝ) + 2 ≤ max (M n) ((n : ℝ) + 2) := le_max_right _ _
      _ ≤ Real.log (r n) := hlogrlarge n
      _ ≤ y n := hylo n
  have hy2 : ∀ n, (2 : ℝ) ≤ y n := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hyn2 n]
  have hypos : ∀ n, 0 < y n := fun n => lt_of_lt_of_le (by norm_num) (hy2 n)
  have hy : Tendsto y atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := exists_nat_ge B
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    calc
      B ≤ (N : ℝ) := hN
      _ ≤ (n : ℝ) := hNn
      _ ≤ (n : ℝ) + 2 := by linarith
      _ ≤ y n := hyn2 n
  have hρ : Tendsto (fun n => Real.exp (y n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hy
  have hd₀pos : 0 < d₀ := by
    by_contra hd₀
    have hd₀zero : d₀ = 0 := Nat.eq_zero_of_not_pos hd₀
    obtain ⟨s, hsC, hsbound⟩ := hlower (C₀ + 1)
    rw [hd₀zero, pow_zero, mul_one] at hsbound
    linarith
  have hνrpos : ∀ n, 0 < ((centralIndex a (r n) : ℕ) : ℝ) := by
    intro n
    by_contra hν
    have hνzero : ((centralIndex a (r n) : ℕ) : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hν) (Nat.cast_nonneg _)
    have hb := hrlower n
    rw [hνzero, zero_pow (Nat.ne_of_gt hd₀pos), mul_zero] at hb
    exact (not_lt_of_ge hb) (hrpos n)
  have hνmono : ∀ n,
      ((centralIndex a (r n) : ℕ) : ℝ) ≤
        (centralIndex a (Real.exp (y n)) : ℝ) := by
    intro n
    have h := monotone_centralIndex_exp ha hn₀ (hylo n)
    change (centralIndex a (Real.exp (Real.log (r n))) : ℝ) ≤
      (centralIndex a (Real.exp (y n)) : ℝ) at h
    rw [Real.exp_log (hrpos n)] at h
    exact h
  have hνpos : ∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ) :=
    fun n => lt_of_lt_of_le (hνrpos n) (hνmono n)
  let c₀ : ℝ := Real.log C₀ + Nevanlinna.borelWindow (1 / 4) + 1
  have hc₀err : Tendsto (fun n => c₀ / y n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := c₀) (f := atTop)).div_atTop hy
  let slope : ℕ → ℝ := fun n =>
    Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n
  have hlowerSlope : ∀ n, c₀ / y n < 1 / 2 →
      (1 : ℝ) / (2 * d₀) ≤ slope n := by
    intro n herr
    have hloglower := Real.log_le_log (hrpos n) (hrlower n)
    rw [Real.log_mul (ne_of_gt hC₀) (pow_ne_zero _ (ne_of_gt (hνrpos n))),
      Real.log_pow] at hloglower
    have hlogmono := Real.log_le_log (hνrpos n) (hνmono n)
    have herr' := (div_lt_iff₀ (hypos n)).mp herr
    have hkey : y n < 2 * (d₀ : ℝ) *
        Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) := by
      dsimp [c₀] at herr'
      have hybound := hyhi' n
      nlinarith
    dsimp [slope]
    apply (le_div_iff₀ (hypos n)).2
    have hdreal : (0 : ℝ) < d₀ := by exact_mod_cast hd₀pos
    calc
      (1 / (2 * (d₀ : ℝ))) * y n = y n / (2 * (d₀ : ℝ)) := by ring
      _ ≤ Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d₀ : ℝ))).2
        nlinarith [hkey]
  have hlowerEventually : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / (2 * d₀) ≤ slope n := by
    filter_upwards [hc₀err.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    exact hlowerSlope n hn
  have hupperAlong : ∀ᶠ n : ℕ in atTop,
      ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) ≤
        C₁ * (Real.exp (y n)) ^ K := hρ.eventually hupper
  have hC₁err : Tendsto (fun n => Real.log C₁ / y n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := Real.log C₁) (f := atTop)).div_atTop hy
  have hupperSlope : ∀ᶠ n : ℕ in atTop, slope n ≤ (K : ℝ) + 1 := by
    filter_upwards [hupperAlong, hC₁err.eventually_lt_const one_pos] with n hν herr
    have hlog := Real.log_le_log (hνpos n) hν
    rw [Real.log_mul (ne_of_gt hC₁) (pow_ne_zero _ (ne_of_gt (Real.exp_pos _))),
      Real.log_pow, Real.log_exp] at hlog
    have herr' := (div_lt_iff₀ (hypos n)).mp herr
    dsimp [slope]
    apply (div_le_iff₀ (hypos n)).2
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlowerEventually.and hupperSlope)
  let p : ℕ → Fin 1 → ℝ := fun n _ => slope (n + N)
  have hp : ∀ n k, p n k ∈ Set.Icc ((1 : ℝ) / (2 * d₀)) ((K : ℝ) + 1) := by
    intro n k
    exact hN (n + N) (by omega)
  obtain ⟨ns, hns, plim, hplim, htendsto⟩ :=
    exists_subseq_tendsto_of_mem_Icc (p := p) hp
  let idx : ℕ → ℕ := fun n => ns n + N
  let y' : ℕ → ℝ := fun n => y (idx n)
  let z' : ℕ → ℂ := fun n => z (idx n)
  let q : ℝ := plim 0
  have hidx : Tendsto idx atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop B] with n hn
    dsimp [idx]
    omega
  have hqpos : 0 < q := by
    have hqmem := hplim 0
    have hdreal : (0 : ℝ) < d₀ := by exact_mod_cast hd₀pos
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 : ℝ) / (2 * d₀)) hqmem.1
  have hδden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := exists_nat_ge B
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div_atTop hδden
  have htoplim : Tendsto (fun n =>
      ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
        (A p).eval (z' n) *
          (deriv (coeffFun a) (z' n) / coeffFun a (z' n)) ^ p.2‖)
      atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ (hδ.comp hidx)
    filter_upwards with n
    exact htop (idx n)
  have hdefectlim : Tendsto (fun n =>
      ‖z' n * deriv (coeffFun a) (z' n) / coeffFun a (z' n) -
        (centralIndex a (Real.exp (y' n)) : ℂ)‖ /
          (centralIndex a (Real.exp (y' n)) : ℝ)) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (hνpos _).le)
      ?_ (hδ.comp hidx)
    filter_upwards with n
    dsimp [y', z']
    apply (div_le_iff₀ (hνpos (idx n))).2
    exact hdefect (idx n)
  refine ⟨S, A, d, m, y', z', q, hdeg, hrel, hmpos, hmle, htarget, htopdeg,
    hAne, hAdeg, hqpos, hρ.comp hidx, ?_, fun n => hνpos (idx n), ?_, htoplim,
    hdefectlim, hpoly, hshift⟩
  · intro n
    exact hz (idx n)
  · have hq := htendsto 0
    simpa [y', q, p, slope, idx] using hq

/-- Existential wrapper around `exists_firstOrderWimanTopRelationSlope_of_relation`. -/
theorem exists_firstOrderWimanTopRelationSlope
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d m : ℕ)
        (y : ℕ → ℝ) (z : ℕ → ℂ) (q : ℝ),
      (∀ p ∈ S, p.1 + p.2 ≤ d) ∧
      (∀ w : ℂ,
        ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 *
          (deriv (coeffFun a) w) ^ p.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      0 < q ∧ Tendsto (fun n => Real.exp (y n)) atTop atTop ∧
      (∀ n, ‖z n‖ = Real.exp (y n)) ∧
      (∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ)) ∧
      Tendsto (fun n => Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n)
        atTop (nhds q) ∧
      Tendsto (fun n =>
        ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
          (A p).eval (z n) * (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ p.2‖)
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        ‖z n * deriv (coeffFun a) (z n) / coeffFun a (z n) -
          (centralIndex a (Real.exp (y n)) : ℂ)‖ /
            (centralIndex a (Real.exp (y n)) : ℝ)) atTop (nhds 0) ∧
      ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧
        (∀ w : ℂ, MvPolynomial.eval
          (Fin.cons w fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) w) P = 0) ∧
        firstOrderMvPoly S A =
          MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
        IsPositiveDerivativeCoefficientShift P S A d := by
  obtain ⟨P, hP, hPrel⟩ := hDA
  obtain ⟨S, A, d, m, y, z, q, hdeg, hrel, hmpos, hmle, hmem, htop, hAne,
    hAdeg, hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim, hpoly, hshift⟩ :=
      exists_firstOrderWimanTopRelationSlope_of_relation ha hn₀ htrans P hP hPrel
  exact ⟨S, A, d, m, y, z, q, hdeg, hrel, hmpos, hmle, hmem, htop, hAne, hAdeg,
    hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim, P, hP, hPrel, hpoly,
    hshift⟩

end

end GaloisForLFunctions.HTGeometry
