import GaloisForLFunctions.HTGeometry.PolyaPopkenDenominator
import GaloisForLFunctions.HTGeometry.EulerADEConjugate
import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation

/-!
# Popken's lower bound for nonzero algebraic Taylor coefficients

Pólya's denominator weight, Maillet's bound for every conjugate and the Liouville separation for a
nonzero algebraic integer combine into Popken's estimate: a nonzero coefficient of a formal
solution of an integral Euler differential equation whose coefficients are algebraic has modulus at
least `exp(-K n (log n)^2)`.
-/

open PowerSeries MvPolynomial NumberField

namespace GaloisForLFunctions.HTGeometry

/-! ### Domination by `n (log n)^2` -/

theorem exists_dominating_const (a b c d : ℝ) :
    ∃ Kp : ℝ, 0 < Kp ∧ ∀ n : ℕ, 2 ≤ n →
      a + b * (n : ℝ) + c * ((n : ℝ) * Real.log n) + d * ((n : ℝ) * (Real.log n) ^ 2)
        ≤ Kp * ((n : ℝ) * (Real.log n) ^ 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|a| / (2 * (Real.log 2) ^ 2) + |b| / (Real.log 2) ^ 2 + |c| / Real.log 2 + |d| + 1,
    by positivity, ?_⟩
  intro n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hLpos : 0 < Real.log n := lt_of_lt_of_le hl2 hL
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set L : ℝ := Real.log n with hLdef
  set X : ℝ := (n : ℝ) * L ^ 2 with hXdef
  have hXpos : 0 < X := by positivity
  have hX2 : 2 * (Real.log 2) ^ 2 ≤ X := by
    have h1 : (Real.log 2) ^ 2 ≤ L ^ 2 := by nlinarith
    nlinarith
  -- each term is dominated
  have ha : a ≤ |a| / (2 * (Real.log 2) ^ 2) * X := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : |a| ≤ |a| / (2 * (Real.log 2) ^ 2) * X := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg a]
    linarith
  have hb : b * (n : ℝ) ≤ |b| / (Real.log 2) ^ 2 * X := by
    have h1 : b * (n : ℝ) ≤ |b| * (n : ℝ) := by
      have := le_abs_self b
      nlinarith
    have h2 : |b| * (n : ℝ) ≤ |b| / (Real.log 2) ^ 2 * X := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), hXdef]
      have h3 : (Real.log 2) ^ 2 ≤ L ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3
        (mul_nonneg (abs_nonneg b) (le_of_lt hnpos))
      nlinarith [h4]
    linarith
  have hc : c * ((n : ℝ) * L) ≤ |c| / Real.log 2 * X := by
    have h1 : c * ((n : ℝ) * L) ≤ |c| * ((n : ℝ) * L) := by
      have := le_abs_self c
      nlinarith [mul_nonneg (le_of_lt hnpos) (le_of_lt hLpos)]
    have h2 : |c| * ((n : ℝ) * L) ≤ |c| / Real.log 2 * X := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2, hXdef]
      have h4 := mul_le_mul_of_nonneg_left hL
        (mul_nonneg (mul_nonneg (abs_nonneg c) (le_of_lt hnpos)) (le_of_lt hLpos))
      nlinarith [h4]
    linarith
  have hd : d * X ≤ |d| * X := by
    have := le_abs_self d
    nlinarith
  have hfinal : (0 : ℝ) ≤ X := le_of_lt hXpos
  nlinarith [ha, hb, hc, hd, hfinal]

/-! ### Transfers along the embedding of an intermediate field -/

theorem isIntegral_of_coe {K : IntermediateField ℚ ℂ} {x : K}
    (h : IsIntegral ℤ ((x : ℂ))) : IsIntegral ℤ x := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p, hm, ?_⟩
  have hinj : Function.Injective (K.val : K →ₐ[ℚ] ℂ) := K.val.injective
  apply hinj
  rw [map_zero, ← hp]
  have hev := Polynomial.hom_eval₂ p (algebraMap ℤ K) (K.val : K →ₐ[ℚ] ℂ).toRingHom x
  simp only [AlgHom.toRingHom_eq_coe] at hev
  rw [show ((K.val : K →ₐ[ℚ] ℂ) : K →+* ℂ).comp (algebraMap ℤ K) = algebraMap ℤ ℂ from
    RingHom.ext_int _ _] at hev
  exact hev

theorem isAlgebraic_of_mem_intermediateField {K : IntermediateField ℚ ℂ}
    (h : FiniteDimensional ℚ K) {x : ℂ} (hx : x ∈ K) : IsAlgebraic ℚ x := by
  haveI := h
  have h1 : IsAlgebraic ℚ (⟨x, hx⟩ : K) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p, hp0, hp⟩ := h1
  refine ⟨p, hp0, ?_⟩
  have hev := Polynomial.aeval_algHom_apply (K.val : K →ₐ[ℚ] ℂ) (⟨x, hx⟩ : K) p
  simp only [hp, map_zero] at hev
  simpa using hev

/-! ### Denominators for the inverse indicial values -/

/-- **Denominators of the reciprocal indicial values.**  The absolute norms of the values of the
indicial polynomial are denominators for their inverses and grow at most polynomially. -/
theorem exists_indicial_denominator {K : IntermediateField ℚ ℂ} (hKfin : FiniteDimensional ℚ K)
    {m N : ℕ} (b : Fin (m + 1) → ℂ) (hbK : ∀ i, b i ∈ K)
    (hLne : ∀ q, 1 ≤ q → (∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ)) ≠ 0) :
    ∃ (A : ℕ → ℕ) (bnd : ℝ) (dg : ℕ), (∀ q, 0 < A q) ∧ 0 < bnd ∧
      (∀ q, 1 ≤ q → IsIntegral ℤ ((A q : ℂ) /
        ∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ))) ∧
      (∀ q, 1 ≤ q → (A q : ℝ) ≤ bnd * ((q : ℝ) + 1) ^ dg) := by
  classical
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := hKfin }
  -- a common denominator for the coefficients of the indicial polynomial
  have hbalg : ∀ i, IsAlgebraic ℚ (b i) := fun i =>
    isAlgebraic_of_mem_intermediateField hKfin (hbK i)
  choose db hdb hdbd using fun i => exists_denBy (hbalg i)
  set dL : ℕ := ∏ i : Fin (m + 1), db i with hdLdef
  have hdL : 0 < dL := Finset.prod_pos fun i _ => hdb i
  have hdLint : ∀ i, IsIntegral ℤ ((dL : ℂ) * b i) := by
    intro i
    have := (hdbd i).mono (Finset.dvd_prod_of_mem db (Finset.mem_univ i))
    exact this
  -- the scaled indicial value, as an element of the number field
  set bK : Fin (m + 1) → K := fun i => ⟨b i, hbK i⟩ with hbKdef
  set βK : ℕ → K := fun q => (dL : K) * ∑ i : Fin (m + 1), bK i * ((q + N : ℕ) : K) ^ (i : ℕ)
    with hβKdef
  have hβcoe : ∀ q, ((βK q : K) : ℂ)
      = (dL : ℂ) * ∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ) := by
    intro q
    rw [hβKdef]
    push_cast
    rfl
  have hβint : ∀ q, IsIntegral ℤ (βK q) := by
    intro q
    refine isIntegral_of_coe ?_
    rw [hβcoe q, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    have h1 : (dL : ℂ) * (b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ))
        = ((dL : ℂ) * b i) * (((q + N : ℕ) ^ (i : ℕ) : ℕ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    exact (hdLint i).mul (isIntegral_natCast _)
  have hβne : ∀ q, 1 ≤ q → βK q ≠ 0 := by
    intro q hq hzero
    refine hLne q hq ?_
    have h0 : ((βK q : K) : ℂ) = 0 := by rw [hzero]; simp
    rw [hβcoe q] at h0
    have hdLne : ((dL : ℂ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    exact (mul_eq_zero.mp h0).resolve_left hdLne
  -- the absolute norms of the scaled indicial values
  have hall : ∀ q, ∃ Aq : ℕ, 0 < Aq ∧
      (1 ≤ q → (Aq : ℝ) = ∏ σ : K →+* ℂ, ‖σ (βK q)‖) ∧
      (1 ≤ q → IsIntegral ℤ ((Aq : ℂ) / ((βK q : K) : ℂ))) := by
    intro q
    by_cases hq : 1 ≤ q
    · obtain ⟨Aq, hAq, heq, hint⟩ :=
        exists_norm_denominator (βK q) (hβne q hq) (hβint q) (K.val : K →ₐ[ℚ] ℂ).toRingHom
      exact ⟨Aq, hAq, fun _ => heq, fun _ => hint⟩
    · exact ⟨1, one_pos, fun h => absurd h hq, fun h => absurd h hq⟩
  choose A hApos hAeq hAint using hall
  -- the size of the conjugates
  set S : (K →+* ℂ) → ℝ := fun σ => 1 + ∑ i : Fin (m + 1), ‖σ (bK i)‖ with hSdef
  have hSpos : ∀ σ, 0 < S σ := by
    intro σ
    have : 0 ≤ ∑ i : Fin (m + 1), ‖σ (bK i)‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    simp only [hSdef]
    linarith
  have hconjbound : ∀ (σ : K →+* ℂ) (q : ℕ), 1 ≤ q →
      ‖σ (βK q)‖ ≤ (dL : ℝ) * S σ * ((q : ℝ) + 1) ^ m * ((N : ℝ) + 1) ^ m := by
    intro σ q hq
    have hσβ : σ (βK q) = (dL : ℂ) * ∑ i : Fin (m + 1), σ (bK i) * ((q + N : ℕ) : ℂ) ^ (i : ℕ) := by
      rw [hβKdef]
      push_cast
      simp only [map_mul, map_sum, map_pow, map_add, map_natCast]
    rw [hσβ, norm_mul]
    have hnormsum : ‖∑ i : Fin (m + 1), σ (bK i) * ((q + N : ℕ) : ℂ) ^ (i : ℕ)‖
        ≤ ∑ i : Fin (m + 1), ‖σ (bK i)‖ * ((q : ℝ) + N) ^ (i : ℕ) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_pow]
      have : ‖((q + N : ℕ) : ℂ)‖ = (q : ℝ) + N := by
        rw [Complex.norm_natCast]
        push_cast
        ring
      rw [this]
    have hqN : ((q : ℝ) + N) ≤ ((q : ℝ) + 1) * ((N : ℝ) + 1) := by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hpowle : ∀ i : Fin (m + 1), ((q : ℝ) + N) ^ (i : ℕ)
        ≤ (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m := by
      intro i
      have h1 : ((q : ℝ) + N) ^ (i : ℕ) ≤ (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ (i : ℕ) := by
        refine pow_le_pow_left₀ ?_ hqN _
        positivity
      refine le_trans h1 (pow_le_pow_right₀ ?_ (by omega))
      nlinarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) N]
    have hsum2 : ∑ i : Fin (m + 1), ‖σ (bK i)‖ * ((q : ℝ) + N) ^ (i : ℕ)
        ≤ (∑ i : Fin (m + 1), ‖σ (bK i)‖) * (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_left (hpowle i) (norm_nonneg _)
    have hSle : (∑ i : Fin (m + 1), ‖σ (bK i)‖) ≤ S σ := by
      simp only [hSdef]
      linarith
    have hdLnorm : ‖(dL : ℂ)‖ = (dL : ℝ) := by
      rw [Complex.norm_natCast]
    rw [hdLnorm]
    have hpospow : (0 : ℝ) ≤ (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m := by positivity
    have hchain : ‖∑ i : Fin (m + 1), σ (bK i) * ((q + N : ℕ) : ℂ) ^ (i : ℕ)‖
        ≤ S σ * (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m := by
      refine le_trans hnormsum (le_trans hsum2 ?_)
      exact mul_le_mul_of_nonneg_right hSle hpospow
    have hfin : (dL : ℝ) * (S σ * (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m)
        = (dL : ℝ) * S σ * ((q : ℝ) + 1) ^ m * ((N : ℝ) + 1) ^ m := by
      rw [mul_pow]
      ring
    calc (dL : ℝ) * ‖∑ i : Fin (m + 1), σ (bK i) * ((q + N : ℕ) : ℂ) ^ (i : ℕ)‖
        ≤ (dL : ℝ) * (S σ * (((q : ℝ) + 1) * ((N : ℝ) + 1)) ^ m) := by
          refine mul_le_mul_of_nonneg_left hchain ?_
          positivity
      _ = (dL : ℝ) * S σ * ((q : ℝ) + 1) ^ m * ((N : ℝ) + 1) ^ m := hfin
  have hdLne : ((dL : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  refine ⟨A, (∏ σ : K →+* ℂ, ((dL : ℝ) * S σ)) * (((N : ℝ) + 1) ^ m) ^ Fintype.card (K →+* ℂ),
    m * Fintype.card (K →+* ℂ), hApos, ?_, ?_, ?_⟩
  · have h1 : 0 < ∏ σ : K →+* ℂ, ((dL : ℝ) * S σ) := by
      refine Finset.prod_pos fun σ _ => mul_pos ?_ (hSpos σ)
      exact_mod_cast hdL
    positivity
  · intro q hq
    have h1 : (∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ))
        = ((βK q : K) : ℂ) / (dL : ℂ) := by
      rw [hβcoe q]
      field_simp
    have hβne' : ((βK q : K) : ℂ) ≠ 0 := by
      intro hcon
      refine hβne q hq ?_
      have := (K.val : K →ₐ[ℚ] ℂ).injective (a₁ := βK q) (a₂ := 0)
      apply this
      simpa using hcon
    rw [h1]
    have h2 : (A q : ℂ) / (((βK q : K) : ℂ) / (dL : ℂ))
        = (dL : ℂ) * ((A q : ℂ) / ((βK q : K) : ℂ)) := by
      field_simp
    rw [h2]
    exact (isIntegral_natCast dL).mul (hAint q hq)
  · intro q hq
    rw [hAeq q hq]
    have hstep : ∏ σ : K →+* ℂ, ‖σ (βK q)‖
        ≤ ∏ σ : K →+* ℂ, ((dL : ℝ) * S σ * ((q : ℝ) + 1) ^ m * ((N : ℝ) + 1) ^ m) :=
      Finset.prod_le_prod (fun σ _ => norm_nonneg _) (fun σ _ => hconjbound σ q hq)
    refine le_trans hstep (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, pow_mul]
    ring

/-! ### Popken's lower bound -/

set_option maxHeartbeats 1000000 in
/-- **Popken's lower bound.**  A nonzero coefficient of a formal solution of a nondegenerate
integral Euler differential equation whose coefficients lie in a number field has modulus at least
`exp(-K n (log n)^2)`. -/
theorem exists_popken_lower_bound {m : ℕ} (PZ : MvPolynomial (Fin (m + 1)) (PowerSeries ℤ))
    (hP0 : MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ ≠ 0)
    (hPan : IsAnalyticDifferentialPolynomial
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ))
    {F : PowerSeries ℂ}
    (hsol : IsFormalEulerADESolution
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) F)
    (hnd : ∃ j, MvPolynomial.aeval (eulerJetVector F)
      (MvPolynomial.pderiv j (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ)) ≠ 0)
    {K : IntermediateField ℚ ℂ} (hKfin : FiniteDimensional ℚ K)
    (hFK : CoefficientsIn K F) :
    ∃ Kp : ℝ, 0 < Kp ∧ ∀ n : ℕ, 2 ≤ n → PowerSeries.coeff n F ≠ 0 →
      Real.exp (-(Kp * ((n : ℝ) * (Real.log n) ^ 2))) ≤ ‖PowerSeries.coeff n F‖ := by
  classical
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := hKfin }
  set P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ) :=
    MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ with hPdef
  have hPcoeff : ∀ d n, ∃ z : ℤ, PowerSeries.coeff n (MvPolynomial.coeff d P) = (z : ℂ) := by
    intro d n
    refine ⟨PowerSeries.coeff n (MvPolynomial.coeff d PZ), ?_⟩
    rw [hPdef, MvPolynomial.coeff_map, PowerSeries.coeff_map]
    rfl
  have hPbd : ∀ d, BoundedDenSeries (MvPolynomial.coeff d P) := by
    intro d
    refine ⟨1, one_pos, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hPcoeff d n
    rw [hz]
    exact denBy_of_isIntegral (isIntegral_intCast z) 1
  have hPK : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P) := by
    intro d n
    obtain ⟨z, hz⟩ := hPcoeff d n
    rw [hz]
    exact intCast_mem K z
  have halg : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n F) := fun n =>
    isAlgebraic_of_mem_intermediateField hKfin (hFK n)
  obtain ⟨N, e, b, he, hbK, hLne, hden⟩ :=
    exists_mahlerDen_of_nondegenerate_eulerADE P hPbd K hPK halg hFK hsol hnd
  obtain ⟨A, bnd, dg, hApos, hbnd, hAint, hAsize⟩ :=
    exists_indicial_denominator hKfin b hbK hLne
  have hdenom := hden e A he hApos dvd_rfl hAint
  -- the coefficient sequence inside the number field
  set FK : PowerSeries K := PowerSeries.mk fun n => ⟨PowerSeries.coeff n F, hFK n⟩ with hFKdef
  set ιK : K →+* ℂ := (K.val : K →ₐ[ℚ] ℂ).toRingHom with hιdef
  have hFKmap : PowerSeries.map ιK FK = F := by
    ext n
    rw [PowerSeries.coeff_map, hFKdef, PowerSeries.coeff_mk]
    rfl
  obtain ⟨Cb, Ab, r, hCb, hAb, hconj⟩ :=
    exists_uniform_conjugate_gevrey PZ hP0 hPan ιK (by rw [hFKmap]; exact hsol)
  set D : ℕ := Fintype.card (K →+* ℂ) with hDdef
  set Dn : ℕ → ℕ := fun n => e * mahlerScale e A (n - N) with hDndef
  have hDnpos : ∀ n, 0 < Dn n := fun n => mul_pos he (mahlerScale_pos he hApos _)
  set Bn : ℕ → ℝ := fun n => (Dn n : ℝ) * Cb * Ab ^ n *
    ((Nat.factorial n : ℕ) : ℝ) ^ (r : ℝ) with hBndef
  have hBnpos : ∀ n, 0 < Bn n := by
    intro n
    have h1 : (0 : ℝ) < (Dn n : ℝ) := by exact_mod_cast hDnpos n
    have h2 : (0 : ℝ) < Ab ^ n := by positivity
    have h3 : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) ^ (r : ℝ) := factorial_rpow_pos n _
    rw [hBndef]
    positivity
  -- the Liouville separation at each nonzero coefficient
  have hlow : ∀ n : ℕ, PowerSeries.coeff n F ≠ 0 →
      ((Dn n : ℝ) * (Bn n) ^ (D - 1))⁻¹ ≤ ‖PowerSeries.coeff n F‖ := by
    intro n hne
    set βn : K := (Dn n : K) * ⟨PowerSeries.coeff n F, hFK n⟩ with hβndef
    have hβcoe : ((βn : K) : ℂ) = (Dn n : ℂ) * PowerSeries.coeff n F := by
      rw [hβndef]
      push_cast
      rfl
    have hβint : IsIntegral ℤ βn := by
      refine isIntegral_of_coe ?_
      rw [hβcoe]
      exact hdenom n
    have hβne : βn ≠ 0 := by
      intro hcon
      have h0 : ((βn : K) : ℂ) = 0 := by rw [hcon]; simp
      rw [hβcoe] at h0
      have hDne : ((Dn n : ℂ)) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact (hDnpos n).ne'
      exact hne ((mul_eq_zero.mp h0).resolve_left hDne)
    have hβOne : (⟨βn, hβint⟩ : 𝓞 K) ≠ 0 := by
      intro hcon
      exact hβne (congrArg (fun z : 𝓞 K => (z : K)) hcon)
    have hbound : ∀ σ : K →+* ℂ, σ ≠ ιK → ‖σ ((⟨βn, hβint⟩ : 𝓞 K) : K)‖ ≤ Bn n := by
      intro σ _
      have hσ : σ ((⟨βn, hβint⟩ : 𝓞 K) : K) = (Dn n : ℂ) * σ (PowerSeries.coeff n FK) := by
        show σ βn = _
        rw [hβndef]
        rw [map_mul, map_natCast]
        congr 1
        rw [hFKdef, PowerSeries.coeff_mk]
      rw [hσ, norm_mul, Complex.norm_natCast]
      have hc := hconj σ n
      have hDn0 : (0 : ℝ) ≤ (Dn n : ℝ) := Nat.cast_nonneg _
      calc (Dn n : ℝ) * ‖σ (PowerSeries.coeff n FK)‖
          ≤ (Dn n : ℝ) * (Cb * Ab ^ n * ((Nat.factorial n : ℕ) : ℝ) ^ (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hc hDn0
        _ = Bn n := by rw [hBndef]; ring
    have hsep := inv_pow_le_norm_embedding (K := K) ⟨βn, hβint⟩ hβOne ιK (hBnpos n) hbound
    have hDpos : (0 : ℝ) < (Dn n : ℝ) := by exact_mod_cast hDnpos n
    have hsep' : (Bn n ^ (D - 1))⁻¹ ≤ (Dn n : ℝ) * ‖PowerSeries.coeff n F‖ := by
      refine le_trans hsep (le_of_eq ?_)
      show ‖ιK ((Dn n : K) * (⟨PowerSeries.coeff n F, hFK n⟩ : K))‖ = _
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      rfl
    rw [mul_inv]
    have h1 := mul_le_mul_of_nonneg_left hsep' (le_of_lt (inv_pos.mpr hDpos))
    calc (Dn n : ℝ)⁻¹ * (Bn n ^ (D - 1))⁻¹
        ≤ (Dn n : ℝ)⁻¹ * ((Dn n : ℝ) * ‖PowerSeries.coeff n F‖) := h1
      _ = ‖PowerSeries.coeff n F‖ := by
          field_simp
  -- logarithmic bookkeeping
  set Cb' : ℝ := max 0 (Real.log bnd + (dg : ℝ) * Real.log 2) with hCb'def
  have hCb'0 : 0 ≤ Cb' := le_max_left _ _
  have hlogA : ∀ j, 1 ≤ j → Real.log (A j) ≤ Cb' + (dg : ℝ) * Real.log j := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hApos' : (0 : ℝ) < (A j : ℝ) := by exact_mod_cast hApos j
    have h1 : Real.log (A j) ≤ Real.log (bnd * ((j : ℝ) + 1) ^ dg) := by
      refine Real.log_le_log hApos' (hAsize j hj)
    have h2 : Real.log (bnd * ((j : ℝ) + 1) ^ dg)
        = Real.log bnd + (dg : ℝ) * Real.log ((j : ℝ) + 1) := by
      rw [Real.log_mul (ne_of_gt hbnd) (by positivity), Real.log_pow]
    have h3 : Real.log ((j : ℝ) + 1) ≤ Real.log 2 + Real.log j := by
      have h4 : (j : ℝ) + 1 ≤ 2 * (j : ℝ) := by linarith
      have h5 : Real.log ((j : ℝ) + 1) ≤ Real.log (2 * (j : ℝ)) :=
        Real.log_le_log (by linarith) h4
      rwa [Real.log_mul (by norm_num) (by linarith)] at h5
    have hdg0 : (0 : ℝ) ≤ (dg : ℝ) := Nat.cast_nonneg _
    have hle : Real.log bnd + (dg : ℝ) * Real.log ((j : ℝ) + 1)
        ≤ Cb' + (dg : ℝ) * Real.log j := by
      have h6 : (dg : ℝ) * Real.log ((j : ℝ) + 1)
          ≤ (dg : ℝ) * (Real.log 2 + Real.log j) := mul_le_mul_of_nonneg_left h3 hdg0
      have h7 : Real.log bnd + (dg : ℝ) * Real.log 2 ≤ Cb' := le_max_right _ _
      nlinarith [h6, h7]
    linarith [h1, h2 ▸ h1, hle]
  -- the size of the weight
  have hloge : 0 ≤ Real.log e := Real.log_nonneg (by exact_mod_cast he)
  have hlogDn : ∀ n : ℕ, 2 ≤ n → Real.log (Dn n)
      ≤ Real.log e + (n : ℝ) * Real.log e
        + (n : ℝ) * (1 + Real.log n) * (Cb' + (dg : ℝ) * Real.log n) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hmpos : (0 : ℝ) < (mahlerScale e A (n - N) : ℝ) := by
      exact_mod_cast mahlerScale_pos he hApos (n - N)
    have hsplit : Real.log (Dn n) = Real.log e + Real.log (mahlerScale e A (n - N)) := by
      rw [hDndef]
      push_cast
      have hene : ((e : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
        exact ne_of_gt this
      rw [Real.log_mul hene (ne_of_gt hmpos)]
    have hms := log_mahlerScale_le (C := e) (A := A) he hApos hCb'0
      (Nat.cast_nonneg dg) hlogA (n - N)
    have hqn : ((n - N : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : (n - N : ℕ) ≤ n := Nat.sub_le n N
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ ((n - N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlogq : Real.log ((n - N : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (n - N) with h | h
      · rw [h]
        simpa using Real.log_nonneg hn1
      · refine Real.log_le_log ?_ hqn
        exact_mod_cast h
    have hlogq0 : 0 ≤ Real.log ((n - N : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (n - N) with h | h
      · rw [h]; simp
      · refine Real.log_nonneg ?_
        exact_mod_cast h
    have hstep1 : ((n - N : ℕ) : ℝ) * Real.log e ≤ (n : ℝ) * Real.log e :=
      mul_le_mul_of_nonneg_right hqn hloge
    have hstep2 : ((n - N : ℕ) : ℝ) * (1 + Real.log ((n - N : ℕ) : ℝ)) *
        (Cb' + (dg : ℝ) * Real.log ((n - N : ℕ) : ℝ))
        ≤ (n : ℝ) * (1 + Real.log n) * (Cb' + (dg : ℝ) * Real.log n) := by
      have hdg0 : (0 : ℝ) ≤ (dg : ℝ) := Nat.cast_nonneg _
      have hA1 : ((n - N : ℕ) : ℝ) * (1 + Real.log ((n - N : ℕ) : ℝ))
          ≤ (n : ℝ) * (1 + Real.log n) := by
        have h1 : (0 : ℝ) ≤ 1 + Real.log ((n - N : ℕ) : ℝ) := by linarith
        have h2 : 1 + Real.log ((n - N : ℕ) : ℝ) ≤ 1 + Real.log n := by linarith
        nlinarith [hq0, hqn, h1, h2]
      have hB1 : Cb' + (dg : ℝ) * Real.log ((n - N : ℕ) : ℝ)
          ≤ Cb' + (dg : ℝ) * Real.log n := by nlinarith [hlogq, hdg0]
      have hB0 : 0 ≤ Cb' + (dg : ℝ) * Real.log ((n - N : ℕ) : ℝ) := by
        nlinarith [hCb'0, hdg0, hlogq0]
      have hA0 : 0 ≤ ((n - N : ℕ) : ℝ) * (1 + Real.log ((n - N : ℕ) : ℝ)) := by
        nlinarith [hq0, hlogq0]
      nlinarith [hA1, hB1, hA0, hB0]
    rw [hsplit]
    linarith [hms, hstep1, hstep2]
  set Dr : ℝ := ((D - 1 : ℕ) : ℝ) with hDrdef
  have hDr0 : 0 ≤ Dr := Nat.cast_nonneg _
  obtain ⟨Kp, hKp, hdom⟩ := exists_dominating_const
    ((1 + Dr) * Real.log e + Dr * Real.log Cb)
    ((1 + Dr) * (Real.log e + Cb') + Dr * Real.log Ab)
    ((1 + Dr) * ((dg : ℝ) + Cb') + Dr * (r : ℝ))
    ((1 + Dr) * (dg : ℝ))
  refine ⟨Kp, hKp, ?_⟩
  intro n hn hne
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hpos : 0 < ‖PowerSeries.coeff n F‖ := norm_pos_iff.mpr hne
  have hDpos : (0 : ℝ) < (Dn n : ℝ) := by exact_mod_cast hDnpos n
  have hfac : Real.log (Nat.factorial n) ≤ (n : ℝ) * Real.log n := by
    have h1 : ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    have h2 : Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
      refine Real.log_le_log ?_ h1
      have : (0 : ℕ) < Nat.factorial n := Nat.factorial_pos n
      exact_mod_cast this
    rwa [Real.log_pow] at h2
  -- the logarithm of the Liouville bound
  have h1 := hlow n hne
  have h2 : Real.log (((Dn n : ℝ) * Bn n ^ (D - 1))⁻¹) ≤ Real.log ‖PowerSeries.coeff n F‖ := by
    refine Real.log_le_log ?_ h1
    have : (0 : ℝ) < Bn n ^ (D - 1) := pow_pos (hBnpos n) _
    positivity
  rw [Real.log_inv] at h2
  have h3 : Real.log ((Dn n : ℝ) * Bn n ^ (D - 1))
      = Real.log (Dn n) + Dr * Real.log (Bn n) := by
    rw [Real.log_mul (ne_of_gt hDpos) (by positivity), Real.log_pow]
  have h4 : Real.log (Bn n) = Real.log (Dn n) + Real.log Cb + (n : ℝ) * Real.log Ab
      + (r : ℝ) * Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    have hf : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by
      have : (0 : ℕ) < Nat.factorial n := Nat.factorial_pos n
      exact_mod_cast this
    have hAbpos : (0 : ℝ) < Ab := by linarith
    rw [hBndef]
    rw [Real.log_mul (by positivity) (ne_of_gt (factorial_rpow_pos n _)),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hDpos) (ne_of_gt hCb),
      Real.log_pow, Real.log_rpow hf]
  -- the elementary upper bound on the logarithms
  have hlogDnn := hlogDn n hn
  have hlogAb0 : 0 ≤ Real.log Ab := Real.log_nonneg hAb
  have hkey : Real.log (Dn n) + Dr * Real.log (Bn n)
      ≤ ((1 + Dr) * Real.log e + Dr * Real.log Cb)
        + ((1 + Dr) * (Real.log e + Cb') + Dr * Real.log Ab) * (n : ℝ)
        + ((1 + Dr) * ((dg : ℝ) + Cb') + Dr * (r : ℝ)) * ((n : ℝ) * Real.log n)
        + ((1 + Dr) * (dg : ℝ)) * ((n : ℝ) * (Real.log n) ^ 2) := by
    have hexp : Real.log e + (n : ℝ) * Real.log e
        + (n : ℝ) * (1 + Real.log n) * (Cb' + (dg : ℝ) * Real.log n)
        = Real.log e + (Real.log e + Cb') * (n : ℝ)
          + ((dg : ℝ) + Cb') * ((n : ℝ) * Real.log n)
          + (dg : ℝ) * ((n : ℝ) * (Real.log n) ^ 2) := by ring
    rw [hexp] at hlogDnn
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have hfacmul : (r : ℝ) * Real.log ((Nat.factorial n : ℕ) : ℝ)
        ≤ (r : ℝ) * ((n : ℝ) * Real.log n) := mul_le_mul_of_nonneg_left hfac hr0
    rw [h4]
    nlinarith [hlogDnn, hfacmul, hDr0, hlogn0, hn1]
  have hfinal : -(Kp * ((n : ℝ) * (Real.log n) ^ 2)) ≤ Real.log ‖PowerSeries.coeff n F‖ := by
    have hdomn := hdom n hn
    have : Real.log ((Dn n : ℝ) * Bn n ^ (D - 1)) ≤ Kp * ((n : ℝ) * (Real.log n) ^ 2) := by
      rw [h3]
      linarith [hkey, hdomn]
    linarith [h2, this]
  calc Real.exp (-(Kp * ((n : ℝ) * (Real.log n) ^ 2)))
      ≤ Real.exp (Real.log ‖PowerSeries.coeff n F‖) := Real.exp_le_exp.mpr hfinal
    _ = ‖PowerSeries.coeff n F‖ := Real.exp_log hpos

end GaloisForLFunctions.HTGeometry
