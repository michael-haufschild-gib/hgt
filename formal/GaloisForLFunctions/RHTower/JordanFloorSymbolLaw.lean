import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.FloorTransformWienerClass
import GaloisForLFunctions.RHTower.GammaShiftZetaReadout
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# The Jordan symbol law of the logarithmically lifted floor transform

For `k ≥ 0` the logarithmically lifted floor transform of a profile `R` is

`(T_k R)(N) = ∑_{d ≤ N} (log d)^k R(⌊N/d⌋)`.

If `R` is the summatory function of a source `a`, floor associativity identifies `T_k R` with the
summatory function of the Dirichlet convolution `(log·)^k ⋆ a`, so the Abel tail of `T_k R` is the
`L`-series of that convolution.  Multiplicativity of `L`-series then gives the exact symbol law

`Abel(T_k R)(s) = (−1)^k ζ^{(k)}(s) · Abel(R)(s)`,

the discrete form of `(T_k R)^(s) = (−1)^k ζ^{(k)}(s) R^(s)`.  At a zeta zero of multiplicity `m`
the multiplier vanishes for `k < m` and not for `k = m`, so the mode annihilated by the plain floor
transform is exposed by its first nonzero Jordan lift.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-! ## The logarithmic jet weight -/

/-- The `k`-th logarithmic jet weight `(log d)^k`. -/
def jetWeight (k d : ℕ) : ℝ := (Real.log d) ^ k

/-- The complex jet weight. -/
def jetWeightC (k : ℕ) : ℕ → ℂ := fun d => ((jetWeight k d : ℝ) : ℂ)

theorem jetWeight_nonneg {k d : ℕ} (hd : 1 ≤ d) : 0 ≤ jetWeight k d := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact pow_nonneg (Real.log_nonneg hd1) k

theorem jetWeightC_eq_iterate (k : ℕ) :
    jetWeightC k = LSeries.logMul^[k] (1 : ℕ → ℂ) := by
  induction k with
  | zero => funext n; simp [jetWeightC, jetWeight]
  | succ k ih =>
    funext n
    rw [Function.iterate_succ_apply', ← ih]
    simp [jetWeightC, jetWeight, LSeries.logMul]
    ring

theorem abscissaOfAbsConv_jetWeightC (k : ℕ) :
    LSeries.abscissaOfAbsConv (jetWeightC k) = 1 := by
  rw [jetWeightC_eq_iterate]
  induction k with
  | zero => simpa using LSeries.abscissaOfAbsConv_one
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

theorem lseriesSummable_jetWeightC (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (jetWeightC k) s := by
  refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
  rw [abscissaOfAbsConv_jetWeightC]
  exact_mod_cast hs

/-- **The Dirichlet series of the jet weight is the signed zeta jet.** -/
theorem LSeries_jetWeightC (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (jetWeightC k) s = (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hone : jetWeightC 0 = (1 : ℕ → ℂ) := by
      funext n
      simp [jetWeightC, jetWeight]
    rw [hone, LSeries_one_eq_riemannZeta hs]
    simp
  · have hpt : ∀ {n : ℕ}, n ≠ 0 →
        jetWeightC k n = (GaloisForLFunctions.zetaJetA k) n := by
      intro n hn
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        simp [jetWeightC, jetWeight, GaloisForLFunctions.zetaJetA, hk.ne']
      · simp [jetWeightC, jetWeight, GaloisForLFunctions.zetaJetA, hn2]
    have hcongr : LSeries (jetWeightC k) s
        = LSeries (⇑(GaloisForLFunctions.zetaJetA k)) s := LSeries_congr hpt s
    rw [hcongr, GaloisForLFunctions.iteratedDeriv_riemannZeta_eq_signed_LSeries k hk hs,
      ← mul_assoc, ← mul_pow]
    simp

/-! ## The floor transform of a summatory profile -/

/-- The unit step profile, vanishing at `0`. -/
def unitStep (j : ℕ) : ℝ := if j = 0 then 0 else 1

theorem sourcePartialSum_eq_floorTransform (a : ℕ → ℝ) (N : ℕ) :
    sourcePartialSum a N = floorTransform a unitStep N := by
  rw [sourcePartialSum, floorTransform]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hq : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).2 hd.2
  rw [unitStep, if_neg (by omega), mul_one]

/-- **Floor associativity for summatory profiles.**  The floor transform of a summatory profile is
the summatory profile of the Dirichlet convolution. -/
theorem floorTransform_sourcePartialSum (w a : ℕ → ℝ) (N : ℕ) :
    floorTransform w (sourcePartialSum a) N = sourcePartialSum (dirichletConv w a) N := by
  have hfun : sourcePartialSum a = floorTransform a unitStep :=
    funext (sourcePartialSum_eq_floorTransform a)
  rw [hfun, floorTransform_comp]
  exact (sourcePartialSum_eq_floorTransform (dirichletConv w a) N).symm

theorem ofReal_dirichletConv (w a : ℕ → ℝ) (n : ℕ) :
    ((dirichletConv w a n : ℝ) : ℂ)
      = LSeries.convolution (fun m => (w m : ℂ)) (fun m => (a m : ℂ)) n := by
  have hconv : LSeries.convolution (fun m => (w m : ℂ)) (fun m => (a m : ℂ)) n
      = ∑ p ∈ n.divisorsAntidiagonal, ((w p.1 : ℝ) : ℂ) * ((a p.2 : ℝ) : ℂ) := by
    rw [LSeries.convolution_def]
  rw [hconv, Nat.sum_divisorsAntidiagonal (fun x y => ((w x : ℝ) : ℂ) * ((a y : ℝ) : ℂ)),
    dirichletConv, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  push_cast
  ring

/-! ## The growth of the lifted transform -/

/-- Every fixed power of the logarithm is dominated by every positive power. -/
theorem exists_const_log_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (Real.log N) ^ m ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (burnolEventually_log_pow_le_rpow hε m)
  set y : ℝ := max x₀ 1 with hy
  have hy1 : (1 : ℝ) ≤ y := le_max_right _ _
  refine ⟨max 1 ((Real.log y) ^ m), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hCpos : (0 : ℝ) ≤ max 1 ((Real.log y) ^ m) := le_trans zero_le_one (le_max_left _ _)
  rcases le_or_gt x₀ (N : ℝ) with hcase | hcase
  · refine le_trans (hx₀ (N : ℝ) hcase) ?_
    nth_rewrite 1 [← one_mul ((N : ℝ) ^ ε)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hNy : (N : ℝ) ≤ y := le_trans hcase.le (le_max_left _ _)
    have hlog : Real.log N ≤ Real.log y := Real.log_le_log (by linarith) hNy
    have hlognn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
    calc (Real.log N) ^ m ≤ (Real.log y) ^ m := pow_le_pow_left₀ hlognn hlog m
      _ ≤ max 1 ((Real.log y) ^ m) := le_max_right _ _
      _ ≤ max 1 ((Real.log y) ^ m) * (N : ℝ) ^ ε := le_mul_of_one_le_right hCpos hrp

/-- **The lifted transform of a polynomially bounded profile.**  With exponent at least one the
weight sum costs only a harmonic factor. -/
theorem abs_floorTransform_jetWeight_le {R : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C) (hθ : 1 ≤ θ)
    (hR : ∀ n : ℕ, |R n| ≤ C * (n : ℝ) ^ θ) (k N : ℕ) :
    |floorTransform (jetWeight k) R N|
      ≤ C * ((Real.log N) ^ k + (Real.log N) ^ (k + 1)) * (N : ℝ) ^ θ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [floorTransform, Real.zero_rpow (by linarith : θ ≠ 0)]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlognn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hNθ : (0 : ℝ) ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (by linarith) _
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |jetWeight k d * R (N / d)|
        ≤ (Real.log N) ^ k * (C * (N : ℝ) ^ θ) * (1 / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    have hdN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hd.2
    have hw : |jetWeight k d| ≤ (Real.log N) ^ k := by
      rw [abs_of_nonneg (jetWeight_nonneg hd.1), jetWeight]
      exact pow_le_pow_left₀ (Real.log_nonneg hd1) (Real.log_le_log (by linarith) hdN) k
    have hq : |R (N / d)| ≤ C * (N : ℝ) ^ θ * (1 / (d : ℝ)) := by
      refine le_trans (hR (N / d)) ?_
      have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
      have hpow : ((N / d : ℕ) : ℝ) ^ θ ≤ ((N : ℝ) / (d : ℝ)) ^ θ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
      have hsplit : ((N : ℝ) / (d : ℝ)) ^ θ = (N : ℝ) ^ θ / (d : ℝ) ^ θ :=
        Real.div_rpow (by linarith) (by linarith) θ
      have hdθ : (d : ℝ) ≤ (d : ℝ) ^ θ := by
        nth_rewrite 1 [← Real.rpow_one (d : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hd1 hθ
      have hinv : (1 : ℝ) / (d : ℝ) ^ θ ≤ 1 / (d : ℝ) :=
        one_div_le_one_div_of_le (by linarith) hdθ
      calc C * ((N / d : ℕ) : ℝ) ^ θ ≤ C * ((N : ℝ) ^ θ / (d : ℝ) ^ θ) := by
            rw [← hsplit]
            exact mul_le_mul_of_nonneg_left hpow hC
        _ = C * (N : ℝ) ^ θ * (1 / (d : ℝ) ^ θ) := by ring
        _ ≤ C * (N : ℝ) ^ θ * (1 / (d : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
    rw [abs_mul]
    calc |jetWeight k d| * |R (N / d)|
        ≤ (Real.log N) ^ k * (C * (N : ℝ) ^ θ * (1 / (d : ℝ))) :=
          mul_le_mul hw hq (abs_nonneg _) (by positivity)
      _ = (Real.log N) ^ k * (C * (N : ℝ) ^ θ) * (1 / (d : ℝ)) := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) = harmonicSum N := rfl
  rw [hharm]
  have hlog := harmonicSum_le_one_add_log hN
  have hcoef : (0 : ℝ) ≤ (Real.log N) ^ k * (C * (N : ℝ) ^ θ) := by positivity
  calc (Real.log N) ^ k * (C * (N : ℝ) ^ θ) * harmonicSum N
      ≤ (Real.log N) ^ k * (C * (N : ℝ) ^ θ) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left hlog hcoef
    _ = C * ((Real.log N) ^ k + (Real.log N) ^ (k + 1)) * (N : ℝ) ^ θ := by
        rw [pow_succ]
        ring

/-- **The lifted transform stays polynomially bounded**, at the cost of an arbitrarily small
increase of the exponent. -/
theorem exists_bound_floorTransform_jetWeight {R : ℕ → ℝ} {C θ ε : ℝ} (hC : 0 ≤ C) (hθ : 1 ≤ θ)
    (hR : ∀ n : ℕ, |R n| ≤ C * (n : ℝ) ^ θ) (k : ℕ) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℕ,
      |floorTransform (jetWeight k) R N| ≤ C' * (N : ℝ) ^ (θ + ε) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_const_log_pow_le_rpow k hε
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_const_log_pow_le_rpow (k + 1) hε
  refine ⟨C * (C₁ + C₂), by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hθε : θ + ε ≠ 0 := by positivity
    simp [floorTransform, Real.zero_rpow hθε]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNθ : (0 : ℝ) ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (by linarith) _
  have hsum : (Real.log N) ^ k + (Real.log N) ^ (k + 1) ≤ (C₁ + C₂) * (N : ℝ) ^ ε := by
    have h1 := hb₁ N hN
    have h2 := hb₂ N hN
    nlinarith [h1, h2]
  have hstep : C * ((Real.log N) ^ k + (Real.log N) ^ (k + 1)) * (N : ℝ) ^ θ
      ≤ C * ((C₁ + C₂) * (N : ℝ) ^ ε) * (N : ℝ) ^ θ := by
    have := mul_le_mul_of_nonneg_left hsum hC
    exact mul_le_mul_of_nonneg_right this hNθ
  have hmul : (N : ℝ) ^ ε * (N : ℝ) ^ θ = (N : ℝ) ^ (θ + ε) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  have hfinal : C * ((C₁ + C₂) * (N : ℝ) ^ ε) * (N : ℝ) ^ θ
      = C * (C₁ + C₂) * (N : ℝ) ^ (θ + ε) := by
    rw [← hmul]
    ring
  rw [hfinal] at hstep
  exact le_trans (abs_floorTransform_jetWeight_le hC hθ hR k N) hstep

/-! ## The symbol law -/

/-- **(24.5) The Jordan symbol law.**  The Abel tail of the `k`-th logarithmically lifted floor
transform is the `k`-th zeta jet times the Abel tail of the profile. -/
theorem abelTailSeries_floorTransform_jetWeight (k : ℕ) {a : ℕ → ℝ} {C θ : ℝ} {s : ℂ}
    (hC : 0 ≤ C) (hθ : 1 ≤ θ)
    (hR : ∀ N : ℕ, |sourcePartialSum a N| ≤ C * (N : ℝ) ^ θ)
    (hs : 1 < s.re) (hθs : θ < s.re)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) s) :
    abelTailSeries (floorTransform (jetWeight k) (sourcePartialSum a)) s
      = (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta s * abelTailSeries (sourcePartialSum a) s := by
  set ε : ℝ := (s.re - θ) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  have hθε : θ + ε < s.re := by
    rw [hε]
    linarith
  have hs0 : (0 : ℝ) < s.re := by linarith
  -- the convolution source
  set b : ℕ → ℝ := dirichletConv (jetWeight k) a with hb
  have hfloor : floorTransform (jetWeight k) (sourcePartialSum a) = sourcePartialSum b :=
    funext (floorTransform_sourcePartialSum (jetWeight k) a)
  have hconvC : (fun n => (b n : ℂ))
      = LSeries.convolution (jetWeightC k) (fun n => (a n : ℂ)) := by
    funext n
    rw [hb, ofReal_dirichletConv]
    rfl
  have hbsum : LSeriesSummable (fun n => (b n : ℂ)) s := by
    rw [hconvC]
    exact (lseriesSummable_jetWeightC k hs).convolution ha
  -- the growth of the convolution profile
  obtain ⟨C', hC', hbound⟩ :=
    exists_bound_floorTransform_jetWeight (R := sourcePartialSum a) hC hθ hR k hεpos
  have hbgrowth : ∀ N : ℕ, |sourcePartialSum b N| ≤ C' * (N : ℝ) ^ (θ + ε) := by
    intro N
    have := hbound N
    rwa [hfloor] at this
  -- the two Abel identifications
  have hleft : abelTailSeries (sourcePartialSum b) s = LSeries (fun n => (b n : ℂ)) s :=
    abelTailSeries_sourcePartialSum hC' hbgrowth hs0 hθε hbsum
  have hright : abelTailSeries (sourcePartialSum a) s = LSeries (fun n => (a n : ℂ)) s :=
    abelTailSeries_sourcePartialSum hC hR hs0 hθs ha
  rw [hfloor, hleft, hright, hconvC,
    LSeries_convolution' (lseriesSummable_jetWeightC k hs) ha, LSeries_jetWeightC k hs]

/-- **The Jordan multiplier hierarchy.**  At a zeta zero of multiplicity `m` the symbol of the
`k`-th lift vanishes exactly for `k < m`, so the mode annihilated by every lower lift is exposed by
the `m`-th one. -/
theorem jetSymbol_vanishing_of_analyticOrder {rho : ℂ} {m : ℕ} (hrho : rho ≠ 1)
    (hm : analyticOrderAt riemannZeta rho = (m : ℕ∞)) :
    (∀ k < m, (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta rho = 0)
      ∧ (-1 : ℂ) ^ m * iteratedDeriv m riemannZeta rho ≠ 0 := by
  have han : AnalyticAt ℂ riemannZeta rho :=
    GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hrho
  obtain ⟨hlt, hne⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).1 hm
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hlt k hk, mul_zero]
  · exact mul_ne_zero (pow_ne_zero m (by norm_num)) hne

end

end RHTower
