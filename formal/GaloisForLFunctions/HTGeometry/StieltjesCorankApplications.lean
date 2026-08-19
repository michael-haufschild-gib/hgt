import GaloisForLFunctions.HTGeometry.StieltjesPowerSumRecovery
import GaloisForLFunctions.RHTower.ExpAlgebraicTranscendental
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.PrimeRadialRelativeJetRank
import GaloisForLFunctions.RHTower.ZetaHypertranscendental

/-!
# The corank-one and corank-two rungs of the Stieltjes collapse

`f1-inversion-single-prime-stieltjes-collapse`, §2 and §2″.

Hermite–Lindemann makes the logarithm of an integer at least two transcendental, so a single
multiplier gives a Laurent-coefficient field of transcendence degree exactly one: one Frobenius
collapses the whole Stieltjes tower to a single logarithm.

At corank two the second Laurent coefficient is `(L_p² + L_q²)/(12 L_p L_q) + 1/4`.  Were it
algebraic, the ratio `L_p/L_q` would satisfy a quadratic equation over the algebraic numbers and so
be algebraic, contradicting Gelfond–Schneider.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The corank-one rung -/


/-- **The logarithm of an integer at least two is transcendental** (Hermite–Lindemann). -/
theorem transcendental_log_nat {n : ℕ} (hn : 2 ≤ n) : Transcendental ℚ (Real.log n) := by
  intro halg
  have hpos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hC : IsAlgebraic ℚ ((Real.log n : ℝ) : ℂ) := by
    have h2 := halg.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    have hx : (IsScalarTower.toAlgHom ℚ ℝ ℂ) (Real.log n) = ((Real.log n : ℝ) : ℂ) := by
      simp [Complex.coe_algebraMap]
    rwa [hx] at h2
  have hZ : IsAlgebraic ℤ ((Real.log n : ℝ) : ℂ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hC
  have hne : ((Real.log n : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  have hT := GaloisForLFunctions.RHTower.exp_algebraic_transcendental hZ hne
  have hexp : Complex.exp ((Real.log n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast lt_of_lt_of_le two_pos hn)]
    norm_num
  rw [hexp] at hT
  exact hT ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (isAlgebraic_nat n))

/-- **§2.**  With a single multiplier whose logarithm is transcendental the Laurent-coefficient
field has transcendence degree exactly one. -/
theorem trdeg_stieltjesField_single_eq_one {ℓ : ℝ} (hℓ : Transcendental ℚ ℓ) :
    Algebra.trdeg ℚ ↥(stieltjesField (fun _ : Fin 1 => ℓ)) = 1 := by
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    exact hℓ (by rw [h]; exact isAlgebraic_zero)
  rw [stieltjesField_single_eq hℓ0, logField]
  have hind : AlgebraicIndependent ℚ (fun _ : Fin 1 => ℓ) :=
    algebraicIndependent_unique_type_iff.mpr hℓ
  refine (trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent
    (fun _ : Fin 1 => ℓ) hind).trans ?_
  simp


/-! ## The corank-two rung -/


theorem coeff_two_beurlingBlock_pair :
    PowerSeries.coeff 2 (beurlingBlock 2)
      = MvPolynomial.C (1/12 : ℚ) * (MvPolynomial.X 1) ^ 2
        + MvPolynomial.C (1/4 : ℚ) * (MvPolynomial.X 0) * (MvPolynomial.X 1)
        + MvPolynomial.C (1/12 : ℚ) * (MvPolynomial.X 0) ^ 2 := by
  rw [beurlingBlock_eq_prod, Fin.prod_univ_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [PowerSeries.coeff_rescale, coeff_blockGen]
  norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two, Nat.factorial]
  ring_nf
  rw [← map_pow]
  norm_num

theorem blockCoeffVal_two_pair (L : Fin 2 → ℝ) :
    blockCoeffVal L 2 = (L 0) ^ 2 / 12 + (L 0) * (L 1) / 4 + (L 1) ^ 2 / 12 := by
  rw [blockCoeffVal, coeff_two_beurlingBlock_pair]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  push_cast
  ring_nf
  norm_num
  ring


theorem isAlgebraic_of_quadratic_over_algebraic {s w : ℝ} (hs : IsAlgebraic ℚ s)
    (hw : w ^ 2 - s * w + 1 = 0) : IsAlgebraic ℚ w := by
  have hsA : s ∈ algebraicClosure ℚ ℝ := mem_algebraicClosure_iff.mpr hs
  have hwA : IsAlgebraic ↥(algebraicClosure ℚ ℝ) w := by
    refine ⟨Polynomial.X ^ 2
      - Polynomial.C (⟨s, hsA⟩ : ↥(algebraicClosure ℚ ℝ)) * Polynomial.X + 1, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun p => Polynomial.coeff p 2) h
      simp [Polynomial.coeff_one] at hc
    · simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        map_one]
      show w ^ 2 - s * w + 1 = 0
      exact hw
  haveI : Algebra.IsAlgebraic ℚ ↥(algebraicClosure ℚ ℝ) := algebraicClosure.isAlgebraic ℚ ℝ
  exact hwA.restrictScalars ℚ

theorem stieltjesVal_two_pair {L : Fin 2 → ℝ} (h0 : L 0 ≠ 0) (h1 : L 1 ≠ 0) :
    stieltjesVal L 2 = ((L 0) ^ 2 + (L 1) ^ 2) / (12 * (L 0) * (L 1)) + 1 / 4 := by
  rw [stieltjesVal, blockCoeffVal_two_pair, Fin.prod_univ_two]
  field_simp
  ring

/-- **§2″.**  For two distinct primes the corank-two Laurent coefficient
`(L_p² + L_q²)/(12 L_p L_q) + 1/4` is transcendental. -/
theorem transcendental_stieltjesVal_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (stieltjesVal ![Real.log p, Real.log q] 2) := by
  have hap : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have haq : (0 : ℝ) < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have h0 : (![Real.log p, Real.log q] : Fin 2 → ℝ) 0 = Real.log p := rfl
  have h1 : (![Real.log p, Real.log q] : Fin 2 → ℝ) 1 = Real.log q := rfl
  have hval : stieltjesVal ![Real.log p, Real.log q] 2
      = ((Real.log p) ^ 2 + (Real.log q) ^ 2) / (12 * Real.log p * Real.log q) + 1 / 4 := by
    rw [stieltjesVal_two_pair (by rw [h0]; exact ne_of_gt hap)
      (by rw [h1]; exact ne_of_gt haq), h0, h1]
  intro hAlg
  rw [hval] at hAlg
  have hγ : ((Real.log p) ^ 2 + (Real.log q) ^ 2) / (12 * Real.log p * Real.log q) + 1 / 4
      ∈ algebraicClosure ℚ ℝ := mem_algebraicClosure_iff.mpr hAlg
  have h12 : ((12 : ℝ)) ∈ algebraicClosure ℚ ℝ := by
    have : ((12 : ℝ)) = ((12 : ℚ) : ℝ) := by norm_num
    rw [this]
    exact (algebraicClosure ℚ ℝ).algebraMap_mem _
  have hq4 : ((1 / 4 : ℝ)) ∈ algebraicClosure ℚ ℝ := by
    have : ((1 / 4 : ℝ)) = ((1 / 4 : ℚ) : ℝ) := by norm_num
    rw [this]
    exact (algebraicClosure ℚ ℝ).algebraMap_mem _
  have hsA : ((Real.log p) ^ 2 + (Real.log q) ^ 2) / (Real.log p * Real.log q)
      ∈ algebraicClosure ℚ ℝ := by
    have heq : ((Real.log p) ^ 2 + (Real.log q) ^ 2) / (Real.log p * Real.log q)
        = 12 * ((((Real.log p) ^ 2 + (Real.log q) ^ 2)
            / (12 * Real.log p * Real.log q) + 1 / 4) - 1 / 4) := by
      field_simp
      ring
    rw [heq]
    exact (algebraicClosure ℚ ℝ).mul_mem h12 ((algebraicClosure ℚ ℝ).sub_mem hγ hq4)
  have hs : IsAlgebraic ℚ (((Real.log p) ^ 2 + (Real.log q) ^ 2) / (Real.log p * Real.log q)) :=
    mem_algebraicClosure_iff.mp hsA
  have hw : (Real.log p / Real.log q) ^ 2
      - (((Real.log p) ^ 2 + (Real.log q) ^ 2) / (Real.log p * Real.log q))
        * (Real.log p / Real.log q) + 1 = 0 := by
    field_simp
    ring
  exact GaloisForLFunctions.RHTower.log_ratio_transcendental hq hp hpq.symm
    (isAlgebraic_of_quadratic_over_algebraic hs hw)



/-! ## §4: the Riemann zeta function is not D-finite -/

open GaloisForLFunctions


/-- A function is *D-finite* when it satisfies a nontrivial linear differential equation with
polynomial coefficients. -/
def DFinite (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (q : Fin (m + 1) → Polynomial ℂ), (∃ i, q i ≠ 0) ∧
    ∀ z : ℂ, ∑ i : Fin (m + 1), (q i).eval z * iteratedDeriv (i : ℕ) f z = 0

theorem eval_aeval_X_zero {m : ℕ} (p : Polynomial ℂ) (v : Fin (m + 2) → ℂ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 2))) p)
      = p.eval (v 0) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | monomial n a => simp

/-- **D-finite implies differentially algebraic.**  A linear differential equation with polynomial
coefficients is in particular an algebraic differential equation. -/
theorem differentiallyAlgebraic_of_dFinite {f : ℂ → ℂ} (h : DFinite f) :
    DifferentiallyAlgebraic f := by
  obtain ⟨m, q, ⟨i₀, hi₀⟩, hrel⟩ := h
  classical
  refine ⟨m, (∑ i : Fin (m + 1),
    (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 2))) (q i)) * MvPolynomial.X i.succ :
      MvPolynomial (Fin (m + 2)) ℂ), ?_, ?_⟩
  · obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, (q i₀).eval z₀ ≠ 0 := by
      by_contra hc
      refine hi₀ (Polynomial.funext fun z => ?_)
      have := not_exists.mp hc z
      simpa using not_not.mp this
    intro hP
    set v : Fin (m + 2) → ℂ := fun j => if j = 0 then z₀ else if j = i₀.succ then 1 else 0 with hv
    have hval := congrArg (MvPolynomial.eval v) hP
    rw [map_zero, map_sum] at hval
    have hterm : ∀ i : Fin (m + 1),
        MvPolynomial.eval v
          ((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 2))) (q i)) * MvPolynomial.X i.succ)
          = if i = i₀ then (q i₀).eval z₀ else 0 := by
      intro i
      rw [map_mul, MvPolynomial.eval_X, eval_aeval_X_zero]
      have hv0 : v 0 = z₀ := by
        show (if (0 : Fin (m+2)) = 0 then z₀ else if (0 : Fin (m+2)) = i₀.succ then (1:ℂ) else 0)
          = z₀
        rw [if_pos rfl]
      rw [hv0]
      by_cases h : i = i₀
      · subst h
        have : v i.succ = 1 := by
          show (if i.succ = 0 then z₀ else if i.succ = i.succ then (1:ℂ) else 0) = 1
          rw [if_neg (Fin.succ_ne_zero i), if_pos rfl]
        rw [this, mul_one, if_pos rfl]
      · have hne : i.succ ≠ i₀.succ := fun hc => h (Fin.succ_injective _ hc)
        have : v i.succ = 0 := by
          show (if i.succ = 0 then z₀ else if i.succ = i₀.succ then (1:ℂ) else 0) = 0
          rw [if_neg (Fin.succ_ne_zero i), if_neg hne]
        rw [this, mul_zero, if_neg h]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ i₀] at hval
    simp only [Finset.mem_univ, if_true] at hval
    exact hz₀ hval
  · intro z
    rw [map_sum, ← hrel z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_X, eval_aeval_X_zero]
    have h0 : (Fin.cons (α := fun _ : Fin (m + 2) => ℂ) z
        fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) f z) 0 = z := by simp
    have hs : (Fin.cons (α := fun _ : Fin (m + 2) => ℂ) z
        fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) f z) i.succ
        = iteratedDeriv (i : ℕ) f z := by simp
    rw [h0, hs]

/-- **`ζ` is not D-finite.** -/
theorem not_dFinite_riemannZeta : ¬ DFinite riemannZeta := fun h =>
  hypertranscendental_riemannZeta (differentiallyAlgebraic_of_dFinite h)


end GaloisForLFunctions.HTGeometry

end
