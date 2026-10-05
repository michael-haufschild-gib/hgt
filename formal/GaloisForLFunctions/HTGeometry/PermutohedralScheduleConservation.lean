import GaloisForLFunctions.HTGeometry.SimplexExponentialIntegral
import GaloisForLFunctions.HTGeometry.PermutohedralAlternantFactorization

/-!
# Schedule alternants and the all-grade subset-phase conservation law

For positive grades `λ_1, …, λ_r` and a schedule `π ∈ S_r`, the ordered finite-horizon coefficient
`B_π(t) = ∫_{u ≥ 0, Σu ≤ t} exp(-Σ_k S_k(π) u_k) du` `(AFD.7)`, with suffix sums
`S_k(π) = Σ_{j ≥ k} λ_{π(j)}`, is `(Π_k S_k)⁻¹` times the distribution function of
`X_{S_1} + ⋯ + X_{S_r}`.  Its Laplace transform is `1/(z Π_k (z + S_k))` `(PGE.4)`, so the
source-commutator alternant `F_r = (Π λ_i) Σ_π sgn(π) B_π` `(AFD.8)` has transform
`(Π λ_i) R_r(z;λ)/z = (Π λ_i) Δ_r P_r(z)/(z D_r(z))` `(AFD.11)`.

The subset-phase law is the law of `Σ_{S ≠ ∅} X_{λ_S}` `(AFD.10)`; its distribution function
`H_r` has transform `M_r/(z D_r(z))` with `M_r = Π_{S ≠ ∅} λ_S = (Π λ_i) W_r`, and vanishes at
the origin to order `2^r - 1 > deg P_r`.  Comparing transforms (quasi-polynomials are determined
by their Laplace transforms) gives the conservation law `W_r F_r = Δ_r P_r(∂_t) H_r` on
`[0, ∞)` `(AFD.12)`, at every positive grade configuration.  At a repeated grade the alternant
vanishes, while `H_r` is defined throughout.
-/

open MeasureTheory Set Filter Topology Equiv
open MvPolynomial (aeval)

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

variable {r : ℕ}

/-! ### Schedule coefficients -/

theorem suffixSum_pos {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) (π : Perm (Fin r)) (k : Fin r) :
    0 < suffixSum lam π k :=
  Finset.sum_pos (fun _ _ => hlam _) ⟨k, Finset.mem_Ici.2 le_rfl⟩

/-- The ordered schedule coefficient `B_π(t)` `(PGE.2)`, `(AFD.7)`. -/
def scheduleCoeff (lam : Fin r → ℝ) (π : Perm (Fin r)) (t : ℝ) : ℝ :=
  simplexExp (fun k => suffixSum lam π k) t

/-- The source-commutator alternant `F_r(t) = (Π λ_i) Σ_π sgn(π) B_π(t)` `(PGE.3)`, `(AFD.8)`. -/
def scheduleAlternant (lam : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∏ i, lam i) * ∑ π : Perm (Fin r), (Perm.sign π : ℤ) • scheduleCoeff lam π t

/-- The suffix rates `S_1(π), …, S_r(π)`. -/
def suffixRates (lam : Fin r → ℝ) (π : Perm (Fin r)) : List ℝ :=
  List.ofFn fun k => suffixSum lam π k

theorem scheduleCoeff_eq {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) (π : Perm (Fin r)) {t : ℝ}
    (ht : 0 ≤ t) :
    scheduleCoeff lam π t = (∏ k, suffixSum lam π k)⁻¹ * hypoCDFList (suffixRates lam π) t :=
  simplexExp_eq_hypoCDF _ (suffixSum_pos hlam π) ht

theorem suffixRates_pos {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) (π : Perm (Fin r)) :
    ∀ ρ ∈ suffixRates lam π, 0 < ρ := fun ρ hρ => by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hρ
  exact suffixSum_pos hlam π k

/-- The quasi-polynomial form of `F_r`. -/
def scheduleQP (lam : Fin r → ℝ) : QuasiPolynomial :=
  ((∏ i, lam i : ℝ) : ℂ) • ∑ π : Perm (Fin r),
    (((Perm.sign π : ℤ) : ℂ) * ((∏ k, suffixSum lam π k : ℝ) : ℂ)⁻¹) • hypoQP (suffixRates lam π)

theorem scheduleAlternant_eq_eval {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) :
    (scheduleAlternant lam t : ℂ) = (scheduleQP lam).eval t := by
  rw [scheduleAlternant, scheduleQP, QuasiPolynomial.eval_smul, QuasiPolynomial.eval_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [QuasiPolynomial.eval_smul, ← hypoCDFList_eq_eval, scheduleCoeff_eq hlam π ht]
  push_cast
  ring

theorem re_le_of_mem_support_scheduleQP {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    ∀ μ ∈ (scheduleQP lam).support, μ.re ≤ 0 := by
  intro μ hμ
  rw [scheduleQP] at hμ
  have h1 := Finsupp.support_smul hμ
  obtain ⟨π, -, hπ⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h1)
  exact re_le_of_mem_support_hypoQP (suffixRates_pos hlam π) μ (Finsupp.support_smul hπ)

/-! ### Laplace transforms -/

theorem prod_map_suffixRates {lam : Fin r → ℝ} (π : Perm (Fin r)) (q : ℂ) :
    ((suffixRates lam π).map fun ρ : ℝ => (ρ : ℂ) / (q + (ρ : ℂ))).prod =
      ∏ k, ((suffixSum lam π k : ℝ) : ℂ) / (q + (suffixSum lam π k : ℝ)) := by
  rw [suffixRates, List.map_ofFn, List.prod_ofFn]
  rfl

theorem ne_zero_of_re_pos {q : ℂ} (hq : 0 < q.re) {a : ℝ} (ha : 0 ≤ a) : q + (a : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The complexified grades. -/
def lamC (lam : Fin r → ℝ) : Fin r → ℂ := fun i => (lam i : ℂ)

theorem suffixSum_lamC (lam : Fin r → ℝ) (π : Perm (Fin r)) (k : Fin r) :
    suffixSum (lamC lam) π k = ((suffixSum lam π k : ℝ) : ℂ) := by
  simp [suffixSum, lamC]

theorem laplace_scheduleQP {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {q : ℂ} (hq : 0 < q.re) :
    (scheduleQP lam).laplace q = ((∏ i, lam i : ℝ) : ℂ) * alternant q (lamC lam) / q := by
  have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
  rw [scheduleQP, QuasiPolynomial.laplace_smul, QuasiPolynomial.laplace_sum, alternant,
    mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  have hS : ∀ k, ((suffixSum lam π k : ℝ) : ℂ) ≠ 0 := fun k => by
    exact_mod_cast (suffixSum_pos hlam π k).ne'
  have hqS : ∀ k, q + ((suffixSum lam π k : ℝ) : ℂ) ≠ 0 := fun k =>
    ne_zero_of_re_pos hq (suffixSum_pos hlam π k).le
  have key : ((∏ k, suffixSum lam π k : ℝ) : ℂ)⁻¹ *
      ∏ k, ((suffixSum lam π k : ℝ) : ℂ) / (q + ((suffixSum lam π k : ℝ) : ℂ)) =
        ∏ k, (q + ((suffixSum lam π k : ℝ) : ℂ))⁻¹ := by
    rw [Complex.ofReal_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    field_simp [hS k, hqS k]
  rw [QuasiPolynomial.laplace_smul, laplace_hypoQP (suffixRates_pos hlam π) hq,
    prod_map_suffixRates, zsmul_eq_mul]
  simp_rw [suffixSum_lamC]
  rw [← key]
  ring

/-- **Lemma 2.1, `(PGE.4)`**: `𝓛B_π(z) = 1/(z Π_k (z + S_k(π)))` for `Re z > 0`. -/
theorem laplace_scheduleCoeff {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) (π : Perm (Fin r))
    {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (scheduleCoeff lam π t : ℂ) * Complex.exp (-(z * t)) =
      (z * ∏ k, (z + (suffixSum lam π k : ℝ)))⁻¹ := by
  have hsupp : ∀ μ ∈ (hypoQP (suffixRates lam π)).support, μ.re < z.re := fun μ hμ =>
    (re_le_of_mem_support_hypoQP (suffixRates_pos hlam π) μ hμ).trans_lt hz
  have hcongr : ∫ t in Ioi (0 : ℝ), (scheduleCoeff lam π t : ℂ) * Complex.exp (-(z * t)) =
      ∫ t in Ioi (0 : ℝ), ((∏ k, suffixSum lam π k : ℝ) : ℂ)⁻¹ *
        ((hypoQP (suffixRates lam π)).eval t * Complex.exp (-(z * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [scheduleCoeff_eq hlam π (le_of_lt ht), Complex.ofReal_mul, hypoCDFList_eq_eval]
    push_cast
    ring
  rw [hcongr, integral_const_mul, (QuasiPolynomial.integral_eval_mul_cexp _ hsupp).2,
    laplace_hypoQP (suffixRates_pos hlam π) hz, prod_map_suffixRates]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hS : ∀ k, ((suffixSum lam π k : ℝ) : ℂ) ≠ 0 := fun k => by
    exact_mod_cast (suffixSum_pos hlam π k).ne'
  have hzS : ∀ k, z + ((suffixSum lam π k : ℝ) : ℂ) ≠ 0 := fun k =>
    ne_zero_of_re_pos hz (suffixSum_pos hlam π k).le
  rw [Finset.prod_div_distrib, Complex.ofReal_prod]
  have hP : ∏ k, ((suffixSum lam π k : ℝ) : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hS k
  have hQ : ∏ k, (z + ((suffixSum lam π k : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => hzS k
  field_simp

theorem phases_ne_zero {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {q : ℂ} (hq : 0 < q.re) :
    ∀ S ∈ subsets r, q + ∑ i ∈ S, lamC lam i ≠ 0 := fun S _ => by
  have : ∑ i ∈ S, lamC lam i = ((∑ i ∈ S, lam i : ℝ) : ℂ) := by simp [lamC]
  rw [this]
  exact ne_zero_of_re_pos hq (Finset.sum_nonneg fun i _ => (hlam i).le)

/-- **`(PGE.7)`, `(AFD.11)`**: `𝓛F_r(z) = (Π λ_i) Δ_r P_r(z;λ)/(z D_r(z;λ))` for `Re z > 0`. -/
theorem laplace_scheduleAlternant {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (scheduleAlternant lam t : ℂ) * Complex.exp (-(z * t)) =
      ((∏ i, lam i : ℝ) : ℂ) * delta (lamC lam) * aeval (point z (lamC lam)) (formNumer r) /
        (z * aeval (point z (lamC lam)) (denom r)) := by
  have hsupp : ∀ μ ∈ (scheduleQP lam).support, μ.re < z.re := fun μ hμ =>
    (re_le_of_mem_support_scheduleQP hlam μ hμ).trans_lt hz
  have hcongr : ∫ t in Ioi (0 : ℝ), (scheduleAlternant lam t : ℂ) * Complex.exp (-(z * t)) =
      ∫ t in Ioi (0 : ℝ), (scheduleQP lam).eval t * Complex.exp (-(z * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [scheduleAlternant_eq_eval hlam (le_of_lt ht)]
  rw [hcongr, (QuasiPolynomial.integral_eval_mul_cexp _ hsupp).2, laplace_scheduleQP hlam hz,
    alternant_eq z (lamC lam) (phases_ne_zero hlam hz)]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hD := aeval_denom_ne_zero z (lamC lam) (phases_ne_zero hlam hz)
  field_simp

/-! ### The subset-phase law -/

/-- The subset rates `λ_S`, `S ≠ ∅`. -/
def subsetRates (lam : Fin r → ℝ) : List ℝ :=
  (subsets r).toList.map fun S => ∑ i ∈ S, lam i

/-- The subset-phase law: the law of `Σ_{S ≠ ∅} X_{λ_S}` `(PGE.13)`, `(AFD.10)`. -/
def subsetLaw (lam : Fin r → ℝ) : Measure ℝ := hypoMeasureList (subsetRates lam)

/-- Its distribution function `H_r(t)`. -/
def subsetCDF (lam : Fin r → ℝ) : ℝ → ℝ := hypoCDFList (subsetRates lam)

theorem subsetRates_pos {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    ∀ ρ ∈ subsetRates lam, 0 < ρ := fun ρ hρ => by
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hρ
  rw [Finset.mem_toList] at hS
  exact Finset.sum_pos (fun i _ => hlam i) (Finset.mem_filter.1 hS).2

theorem length_subsetRates (lam : Fin r → ℝ) : (subsetRates lam).length = 2 ^ r - 1 := by
  rw [subsetRates, List.length_map, Finset.length_toList, card_subsets]

theorem hasHalfLineCDF_subsetLaw {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    HasHalfLineCDF (subsetLaw lam) (subsetCDF lam) :=
  hasHalfLineCDF_hypoMeasureList (subsetRates_pos hlam)

theorem isProbabilityMeasure_subsetLaw {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    IsProbabilityMeasure (subsetLaw lam) :=
  isProbabilityMeasure_hypoMeasureList (subsetRates_pos hlam)

/-- `M_r = Π_{S ≠ ∅} λ_S` `(PGE.12)`, `(AFD.9)`. -/
def subsetGradeProd (lam : Fin r → ℝ) : ℝ := ∏ S ∈ subsets r, ∑ i ∈ S, lam i

/-- `W_r = Π_{|S| ≥ 2} λ_S` `(AFD.9)`. -/
def subsetIncidence (lam : Fin r → ℝ) : ℝ :=
  ∏ S ∈ (subsets r).filter (fun S => 2 ≤ S.card), ∑ i ∈ S, lam i

/-- `M_r = (Π λ_i) W_r`. -/
theorem subsetGradeProd_eq (lam : Fin r → ℝ) :
    subsetGradeProd lam = (∏ i, lam i) * subsetIncidence lam := by
  rw [subsetGradeProd, subsetIncidence, ← Finset.prod_filter_mul_prod_filter_not (subsets r)
    (fun S => 2 ≤ S.card), mul_comm]
  congr 1
  have h : (subsets r).filter (fun S => ¬ 2 ≤ S.card) = Finset.univ.map
      ⟨fun i : Fin r => ({i} : Finset (Fin r)), Finset.singleton_injective⟩ := by
    ext S
    simp only [subsets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, not_le]
    constructor
    · rintro ⟨hne, hc⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show S.card = 1 by have := hne.card_pos; omega)
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      simp
  rw [h, Finset.prod_map]
  simp

/-- **`(PGE.14)`, `(AFD.11)`**: `𝓛H_r(z) = M_r/(z D_r(z;λ))` for `Re z > 0`. -/
theorem laplace_subsetQP {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {q : ℂ} (hq : 0 < q.re) :
    (hypoQP (subsetRates lam)).laplace q =
      (subsetGradeProd lam : ℂ) / (q * aeval (point q (lamC lam)) (denom r)) := by
  have hD := aeval_denom_ne_zero q (lamC lam) (phases_ne_zero hlam hq)
  rw [aeval_denom] at hD
  have hS : ∀ S ∈ subsets r, q + ∑ i ∈ S, lamC lam i = q + ((∑ i ∈ S, lam i : ℝ) : ℂ) :=
    fun S _ => by simp [lamC]
  have hq0 : q ≠ 0 := fun h => by rw [h] at hq; simp at hq
  rw [laplace_hypoQP (subsetRates_pos hlam) hq, subsetRates, List.map_map,
    Finset.prod_map_toList, aeval_denom, subsetGradeProd, Finset.prod_congr rfl hS]
  rw [Finset.prod_congr rfl hS] at hD
  simp only [Function.comp_apply]
  rw [Finset.prod_div_distrib, Complex.ofReal_prod]
  field_simp

theorem laplace_subsetCDF {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (subsetCDF lam t : ℂ) * Complex.exp (-(z * t)) =
      (subsetGradeProd lam : ℂ) / (z * aeval (point z (lamC lam)) (denom r)) := by
  have hsupp : ∀ μ ∈ (hypoQP (subsetRates lam)).support, μ.re < z.re := fun μ hμ =>
    (re_le_of_mem_support_hypoQP (subsetRates_pos hlam) μ hμ).trans_lt hz
  simp_rw [subsetCDF, hypoCDFList_eq_eval]
  rw [(QuasiPolynomial.integral_eval_mul_cexp _ hsupp).2, laplace_subsetQP hlam hz]

/-! ### The formation numerator in the time variable -/

/-- `P_r(z;λ)` as a polynomial in `z`. -/
def formPoly (lam : Fin r → ℝ) : Polynomial ℝ :=
  aeval (fun o : Option (Fin r) => o.elim Polynomial.X fun i => Polynomial.C (lam i)) (formNumer r)

theorem eval_map_aeval {σ : Type*} (f : σ → Polynomial ℝ) (g : σ → ℂ) (z : ℂ)
    (hfg : ∀ s, ((f s).map Complex.ofRealHom).eval z = g s) (p : MvPolynomial σ ℚ) :
    ((aeval f p).map Complex.ofRealHom).eval z = aeval g p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    rw [show (algebraMap ℚ (Polynomial ℝ)) a = Polynomial.C (a : ℝ) from rfl]
    simp
  | add p q hp hq => rw [map_add, Polynomial.map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, hfg, map_mul,
      MvPolynomial.aeval_X]

theorem eval_map_formPoly (lam : Fin r → ℝ) (z : ℂ) :
    ((formPoly lam).map Complex.ofRealHom).eval z = aeval (point z (lamC lam)) (formNumer r) :=
  eval_map_aeval _ _ z (fun o => by cases o <;> simp [point, lamC]) _

theorem natDegree_aeval_le {σ : Type*} (f : σ → Polynomial ℝ) (hf : ∀ s, (f s).natDegree ≤ 1)
    (p : MvPolynomial σ ℚ) : (aeval f p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [show (algebraMap ℚ (Polynomial ℝ)) (MvPolynomial.coeff m p) =
    Polynomial.C ((MvPolynomial.coeff m p : ℚ) : ℝ) from rfl, Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hm)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun s _ => ?_
  exact Polynomial.natDegree_pow_le.trans (by nlinarith [hf s])

theorem natDegree_formPoly_le (lam : Fin r → ℝ) :
    (formPoly lam).natDegree ≤ 2 ^ r - 1 - r * (r + 1) / 2 := by
  refine (natDegree_aeval_le _ (fun o => ?_) _).trans (totalDegree_formNumer_le r)
  cases o
  · exact Polynomial.natDegree_X_le
  · simp

/-! ### The conservation law -/

/-- **Theorem 4.1, `(AFD.12)`: all-grade conservation**
`W_r F_r(t) = Δ_r (P_r(∂_t) H_r)(t)` for `t ≥ 0`. -/
theorem subsetPhase_conservation {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) :
    subsetIncidence lam * scheduleAlternant lam t =
      delta lam * ∑ k ∈ Finset.range ((formPoly lam).natDegree + 1),
        (formPoly lam).coeff k * iteratedDeriv k (subsetCDF lam) t := by
  set PC : Polynomial ℂ := (formPoly lam).map Complex.ofRealHom
  have hdeg : PC.natDegree = (formPoly lam).natDegree :=
    Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective _
  set E : QuasiPolynomial := ((subsetIncidence lam : ℝ) : ℂ) • scheduleQP lam -
    ((delta lam : ℝ) : ℂ) • QuasiPolynomial.applyPoly PC (hypoQP (subsetRates lam))
  have hvanish : ∀ j < PC.natDegree,
      (QuasiPolynomial.iterDeriv j (hypoQP (subsetRates lam))).eval 0 = 0 := fun j hj => by
    refine iterDeriv_hypoQP_eval_zero _ j ?_
    rw [length_subsetRates]
    rw [hdeg] at hj
    have h2 := natDegree_formPoly_le lam
    generalize 2 ^ r = N at h2 ⊢
    generalize r * (r + 1) / 2 = M at h2
    omega
  have hE : E = 0 := by
    refine QuasiPolynomial.eq_zero_of_laplace_eq_zero E (A := 0) fun σ hσ => ?_
    have hq : 0 < ((σ : ℂ)).re := by simpa using hσ
    have hsupp : ∀ μ ∈ (hypoQP (subsetRates lam)).support, μ.re < ((σ : ℂ)).re := fun μ hμ =>
      (re_le_of_mem_support_hypoQP (subsetRates_pos hlam) μ hμ).trans_lt hq
    rw [QuasiPolynomial.laplace_sub, QuasiPolynomial.laplace_smul, QuasiPolynomial.laplace_smul,
      QuasiPolynomial.laplace_applyPoly _ _ hsupp hvanish, laplace_scheduleQP hlam hq,
      laplace_subsetQP hlam hq, eval_map_formPoly,
      alternant_eq _ _ (phases_ne_zero hlam hq), subsetGradeProd_eq]
    have hD := aeval_denom_ne_zero (σ : ℂ) (lamC lam) (phases_ne_zero hlam hq)
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have hdelta : delta (lamC lam) = ((delta lam : ℝ) : ℂ) := by
      simp [delta, lamC]
    rw [hdelta]
    push_cast
    field_simp
    ring
  have h := congrArg (fun E => QuasiPolynomial.eval E t) hE
  simp only [E, QuasiPolynomial.eval_sub, QuasiPolynomial.eval_smul, QuasiPolynomial.eval_zero,
    QuasiPolynomial.eval_applyPoly, sub_eq_zero] at h
  rw [← scheduleAlternant_eq_eval hlam ht, hdeg] at h
  have hderiv : ∀ k, iteratedDeriv k (hypoQP (subsetRates lam)).eval t =
      ((iteratedDeriv k (subsetCDF lam) t : ℝ) : ℂ) := fun k => by
    rw [QuasiPolynomial.iteratedDeriv_eval,
      ← QuasiPolynomial.iteratedDeriv_ofReal_eq (hypoCDFList_eq_eval _) k t]
    rfl
  apply Complex.ofReal_injective
  push_cast
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hderiv k, Polynomial.coeff_map]
  rfl

/-! ### Repeated grades -/

/-- At a repeated grade the schedule alternant vanishes. -/
theorem scheduleAlternant_eq_zero_of_eq {lam : Fin r → ℝ} {i j : Fin r} (hij : i ≠ j)
    (h : lam i = lam j) (t : ℝ) : scheduleAlternant lam t = 0 := by
  have hcomp : ∀ π : Perm (Fin r), scheduleCoeff lam (swap i j * π) t = scheduleCoeff lam π t :=
    fun π => by
      have hS : ∀ k, suffixSum lam (swap i j * π) k = suffixSum lam π k := fun k => by
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Perm.coe_mul, Function.comp_apply]
        rcases eq_or_ne (π m) i with hm | hm
        · rw [hm, swap_apply_left, h]
        · rcases eq_or_ne (π m) j with hm' | hm'
          · rw [hm', swap_apply_right, h]
          · rw [swap_apply_of_ne_of_ne hm hm']
      simp only [scheduleCoeff, hS]
  have hsum : ∑ π : Perm (Fin r), (Perm.sign π : ℤ) • scheduleCoeff lam π t = 0 := by
    have h1 := Fintype.sum_equiv (Equiv.mulLeft (swap i j))
      (fun π => (Perm.sign π : ℤ) • scheduleCoeff lam π t)
      (fun π => -((Perm.sign π : ℤ) • scheduleCoeff lam π t)) fun π => by
        simp only [Equiv.coe_mulLeft, hcomp, Perm.sign_mul, Perm.sign_swap hij]
        simp
    rw [Finset.sum_neg_distrib] at h1
    linarith
  rw [scheduleAlternant, hsum, mul_zero]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
