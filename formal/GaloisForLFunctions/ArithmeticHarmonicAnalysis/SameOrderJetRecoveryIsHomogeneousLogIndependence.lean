import GaloisForLFunctions.ArithmeticHarmonicAnalysis.HigherVerticalJets
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.MixedJetMultiplicity
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TwoPrimeHomogeneousLogRigidity
import GaloisForLFunctions.HTGeometry.AffineTranslationStabilizerRigidity
import GaloisForLFunctions.RHTower.LadderNesting
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Same-order jet recovery is homogeneous independence of prime logarithms

Let `F` vanish to order `r` at the point `1` of the torus of prime coordinates. Its `r`-th scalar jet along the
logarithmic flow is the leading form of `F` evaluated at the prime logarithms
(`iteratedDeriv_primeLogTrace_eq_leadingForm`):

  `∂ₛʳ F(pˢ)|₀ = r! Σ_{|a| = r} c_a Π (log pᵢ)^{aᵢ}`.

So the single scalar jet of order `r` recovers all mixed jets of order `r`, for coefficients in `K`, exactly when the
degree-`r` monomials in the logarithms are linearly independent over `K`
(`sameOrderRecovery_iff_linearIndependent`).

* `r = 1`, any prime family, algebraic coefficients: this is Baker's theorem (`sameOrderRecovery_one`).
* Two primes, any `r`, algebraic coefficients: this is Gelfond–Schneider (`sameOrderRecovery_two_primes`).
* Three or more primes, `r ≥ 2`: the recovery statement is the homogeneous independence itself, a consequence of
  Schanuel's conjecture. No Dirichlet-jet algebra can decide it.
-/

open MvPolynomial Finset
noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {n : ℕ}

/-! ## The formal flow -/

/-- The logarithmic flow as a formal power series: `Xᵢ ↦ exp(Lᵢ t)`. -/
def flowSeries (L : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] PowerSeries ℂ :=
  aeval fun i => PowerSeries.rescale (L i) (PowerSeries.exp ℂ)

/-- The weight of a monomial under the flow. -/
def flowWeight (L : Fin n → ℂ) (m : Fin n →₀ ℕ) : ℂ := ∑ i, (m i : ℂ) * L i

theorem prod_rescale_exp (L : Fin n → ℂ) (m : Fin n →₀ ℕ) (S : Finset (Fin n)) :
    ∏ i ∈ S, PowerSeries.rescale (L i) (PowerSeries.exp ℂ) ^ m i =
      PowerSeries.rescale (∑ i ∈ S, (m i : ℂ) * L i) (PowerSeries.exp ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty]
    ext k
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_one, zero_pow_eq]
  | insert i S hi ih =>
    rw [prod_insert hi, sum_insert hi, ih, ← map_pow, PowerSeries.exp_pow_eq_rescale_exp,
      PowerSeries.rescale_rescale, PowerSeries.exp_mul_exp_eq_exp_add]

theorem flowSeries_monomial (L : Fin n → ℂ) (m : Fin n →₀ ℕ) (c : ℂ) :
    flowSeries L (monomial m c) =
      PowerSeries.C c * PowerSeries.rescale (flowWeight L m) (PowerSeries.exp ℂ) := by
  rw [flowSeries, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), prod_rescale_exp]
  rfl

theorem primeLogEuler_add (p : Fin n → ℕ) (F G : MvPolynomial (Fin n) ℂ) :
    primeLogEuler p (F + G) = primeLogEuler p F + primeLogEuler p G := by
  simp only [primeLogEuler, map_add, mul_add, sum_add_distrib]

theorem primeLogEuler_monomial (p : Fin n → ℕ) (m : Fin n →₀ ℕ) (c : ℂ) :
    primeLogEuler p (monomial m c) =
      monomial m (flowWeight (fun i => (Real.log (p i) : ℂ)) m * c) := by
  have hterm (i : Fin n) : C (Real.log (p i) : ℂ) * X i * pderiv i (monomial m c) =
      monomial m ((m i : ℂ) * (Real.log (p i) : ℂ) * c) := by
    rw [pderiv_monomial, mul_assoc, X, monomial_mul, C_mul_monomial]
    by_cases hi : m i = 0
    · simp [hi]
    · have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr hi
      rw [add_comm, tsub_add_cancel_of_le hle]
      congr 1
      ring
  rw [primeLogEuler, sum_congr rfl fun i _ => hterm i, ← map_sum, flowWeight, sum_mul]

theorem iterate_primeLogEuler_add (p : Fin n → ℕ) (k : ℕ) (F G : MvPolynomial (Fin n) ℂ) :
    (primeLogEuler p)^[k] (F + G) = (primeLogEuler p)^[k] F + (primeLogEuler p)^[k] G := by
  induction k generalizing F G with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp]
    rw [primeLogEuler_add, ih]

theorem iterate_primeLogEuler_monomial (p : Fin n → ℕ) (k : ℕ) (m : Fin n →₀ ℕ) (c : ℂ) :
    (primeLogEuler p)^[k] (monomial m c) =
      monomial m (flowWeight (fun i => (Real.log (p i) : ℂ)) m ^ k * c) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp]
    rw [primeLogEuler_monomial, ih]
    congr 1
    ring

/-- The scalar jets of a polynomial along the flow are the coefficients of its formal flow. -/
theorem iteratedDeriv_primeLogTrace_eq_coeff (p : Fin n → ℕ) (F : MvPolynomial (Fin n) ℂ) (k : ℕ) :
    iteratedDeriv k (primeLogTrace p F 1) 0 =
      (k.factorial : ℂ) * PowerSeries.coeff k (flowSeries (fun i => (Real.log (p i) : ℂ)) F) := by
  rw [iteratedDeriv_primeLogTrace, primeLogTrace_zero]
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [iterate_primeLogEuler_monomial, flowSeries_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [Pi.one_apply, one_pow, prod_const_one, mul_one]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simp only [map_div₀, map_one, map_natCast]
    field_simp
  | add F G hF hG =>
    rw [iterate_primeLogEuler_add, map_add, hF, hG, map_add, map_add, mul_add]

/-! ## The leading form -/

/-- The degree-`r` multi-indices. -/
abbrev degreeIndices (n r : ℕ) : Finset (Fin n →₀ ℕ) := finsuppAntidiag (univ : Finset (Fin n)) r

/-- The monomial `Π Lᵢ^{aᵢ}`. -/
def logMonomial (L : Fin n → ℂ) (a : Fin n →₀ ℕ) : ℂ := ∏ i, L i ^ a i

theorem mem_degreeIndices_iff {r : ℕ} {a : Fin n →₀ ℕ} : a ∈ degreeIndices n r ↔ Finsupp.degree a = r := by
  rw [mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  exact ⟨fun h => h.1, fun h => ⟨h, subset_univ _⟩⟩

/-- `exp(Lt) − 1 = t · v`, with `v(0) = L`. -/
theorem exists_flowFactor (L : ℂ) : ∃ v : PowerSeries ℂ, PowerSeries.constantCoeff v = L ∧
    PowerSeries.rescale L (PowerSeries.exp ℂ) - 1 = PowerSeries.X * v := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.rescale L (PowerSeries.exp ℂ) - 1) = 0 := by
    have hc := PowerSeries.coeff_rescale (f := PowerSeries.exp ℂ) (a := L) (n := 0)
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
    rw [map_sub, hc]
    simp
  obtain ⟨v, hv⟩ := PowerSeries.X_dvd_iff.mpr h0
  refine ⟨v, ?_, hv⟩
  have h1 := congrArg (PowerSeries.coeff 1) hv
  rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one,
    show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul] at h1
  simp at h1
  exact h1.symm

/-- **The scalar jet at the order of vanishing is the leading form at the logarithms.** -/
theorem iteratedDeriv_primeLogTrace_eq_leadingForm (p : Fin n → ℕ) {r : ℕ} {F : MvPolynomial (Fin n) ℂ}
    (hF : F ∈ vanishingIdeal ℂ {(1 : Fin n → ℂ)} ^ r) :
    iteratedDeriv r (primeLogTrace p F 1) 0 =
      (r.factorial : ℂ) * ∑ a ∈ degreeIndices n r,
        (mvPolynomialBaseTranslation (1 : Fin n → ℂ) F).coeff a *
          logMonomial (fun i => (Real.log (p i) : ℂ)) a := by
  classical
  set L : Fin n → ℂ := fun i => (Real.log (p i) : ℂ) with hL
  set G := mvPolynomialBaseTranslation (1 : Fin n → ℂ) F with hG
  have hlow := (mem_pointIdeal_pow_iff_centered_coeff F 1 r).mp hF
  choose v hv0 hv using fun i => exists_flowFactor (L i)
  rw [iteratedDeriv_primeLogTrace_eq_coeff]
  congr 1
  have hflow : flowSeries L F = aeval (fun i => PowerSeries.rescale (L i) (PowerSeries.exp ℂ) - 1) G := by
    rw [hG, HTGeometry.aeval_mvPolynomialBaseTranslation]
    simp [flowSeries]
  rw [hflow]
  have hmono (a : Fin n →₀ ℕ) :
      aeval (fun i => PowerSeries.rescale (L i) (PowerSeries.exp ℂ) - 1) (monomial a (G.coeff a)) =
        PowerSeries.X ^ Finsupp.degree a * (PowerSeries.C (G.coeff a) * ∏ i, v i ^ a i) := by
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum]
    simp only [hv, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
    change PowerSeries.C (G.coeff a) * _ = _
    ring
  have hcoeff (a : Fin n →₀ ℕ) :
      PowerSeries.coeff r (aeval (fun i => PowerSeries.rescale (L i) (PowerSeries.exp ℂ) - 1)
        (monomial a (G.coeff a))) =
      if Finsupp.degree a = r then G.coeff a * logMonomial L a else 0 := by
    by_cases hlt : Finsupp.degree a < r
    · rw [hlow a hlt, map_zero, map_zero, map_zero, if_neg hlt.ne]
    · rw [hmono, PowerSeries.coeff_X_pow_mul']
      by_cases heq : Finsupp.degree a = r
      · rw [if_pos heq.le, if_pos heq, heq, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          map_mul, PowerSeries.constantCoeff_C, map_prod]
        simp only [map_pow, hv0, logMonomial]
      · rw [if_neg (by omega), if_neg heq]
  conv_lhs => rw [G.as_sum]
  rw [map_sum, map_sum, sum_congr rfl fun a _ => hcoeff a, ← sum_filter]
  have hsub : G.support.filter (fun a => Finsupp.degree a = r) ⊆ degreeIndices n r := fun a ha =>
    mem_degreeIndices_iff.mpr (mem_filter.mp ha).2
  refine sum_subset hsub fun a ha hna => ?_
  have hdeg := mem_degreeIndices_iff.mp ha
  have hzero : G.coeff a = 0 := by
    by_contra h
    exact hna (mem_filter.mpr ⟨mem_support_iff.mpr h, hdeg⟩)
  rw [hzero, zero_mul]

/-! ## The equivalence -/

/-- **Same-order recovery ⇔ homogeneous independence.** For coefficients in `K`: the scalar jet of order `r` detects
order `r` of vanishing exactly when the degree-`r` monomials in the logarithms are `K`-linearly independent. -/
theorem sameOrderRecovery_iff_linearIndependent (K : Type*) [Field K] [Algebra K ℂ] (p : Fin n → ℕ) (r : ℕ) :
    (∀ F : MvPolynomial (Fin n) ℂ,
        (∀ a, (mvPolynomialBaseTranslation (1 : Fin n → ℂ) F).coeff a ∈ (algebraMap K ℂ).range) →
        F ∈ vanishingIdeal ℂ {(1 : Fin n → ℂ)} ^ r →
        iteratedDeriv r (primeLogTrace p F 1) 0 = 0 →
        F ∈ vanishingIdeal ℂ {(1 : Fin n → ℂ)} ^ (r + 1)) ↔
      LinearIndependent K (fun a : degreeIndices n r => logMonomial (fun i => (Real.log (p i) : ℂ)) a) := by
  classical
  have hfact : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hrec g hg a
    -- The polynomial with leading form `g`.
    let G : MvPolynomial (Fin n) ℂ := ∑ b : degreeIndices n r, monomial (b : Fin n →₀ ℕ) (algebraMap K ℂ (g b))
    let F := (mvPolynomialBaseTranslation (1 : Fin n → ℂ)).symm G
    have hTF : mvPolynomialBaseTranslation (1 : Fin n → ℂ) F = G := AlgEquiv.apply_symm_apply _ _
    have hcoeffG (b : Fin n →₀ ℕ) : G.coeff b =
        if hb : b ∈ degreeIndices n r then algebraMap K ℂ (g ⟨b, hb⟩) else 0 := by
      simp only [G, coeff_sum, coeff_monomial]
      split_ifs with hb
      · rw [sum_eq_single (⟨b, hb⟩ : degreeIndices n r)]
        · simp
        · intro c _ hc
          rw [if_neg]
          exact fun h => hc (Subtype.ext h)
        · simp
      · refine sum_eq_zero fun c _ => ?_
        rw [if_neg]
        rintro rfl
        exact hb c.2
    have hmem : F ∈ vanishingIdeal ℂ {(1 : Fin n → ℂ)} ^ r := by
      rw [mem_pointIdeal_pow_iff_centered_coeff, hTF]
      intro b hb
      rw [hcoeffG, dif_neg]
      intro h
      exact hb.ne (mem_degreeIndices_iff.mp h)
    have hK : ∀ b, (mvPolynomialBaseTranslation (1 : Fin n → ℂ) F).coeff b ∈ (algebraMap K ℂ).range := by
      intro b
      rw [hTF, hcoeffG]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact zero_mem _
    have hjet : iteratedDeriv r (primeLogTrace p F 1) 0 = 0 := by
      rw [iteratedDeriv_primeLogTrace_eq_leadingForm p hmem, hTF]
      have hthis : ∑ b : degreeIndices n r, G.coeff b * logMonomial (fun i => (Real.log (p i) : ℂ)) b =
          ∑ b : degreeIndices n r, g b • logMonomial (fun i => (Real.log (p i) : ℂ)) b := by
        refine sum_congr rfl fun b _ => ?_
        rw [hcoeffG, dif_pos b.2, Algebra.smul_def]
      have he := sum_coe_sort (degreeIndices n r)
        (fun a => G.coeff a * logMonomial (fun i => (Real.log (p i) : ℂ)) a)
      rw [← he, hthis, hg, mul_zero]
    have hnext := (mem_pointIdeal_pow_iff_centered_coeff F 1 (r + 1)).mp (hrec F hK hmem hjet)
    have h0 := hnext a (by rw [mem_degreeIndices_iff.mp a.2]; omega)
    rw [hTF, hcoeffG, dif_pos a.2] at h0
    exact (FaithfulSMul.algebraMap_injective K ℂ) (by rw [h0, map_zero])
  · intro hind F hK hF hjet
    rw [iteratedDeriv_primeLogTrace_eq_leadingForm p hF] at hjet
    have hsum := (mul_eq_zero.mp hjet).resolve_left hfact
    have hK' : ∀ a, ∃ k : K, algebraMap K ℂ k =
        (mvPolynomialBaseTranslation (1 : Fin n → ℂ) F).coeff a := fun a => RingHom.mem_range.mp (hK a)
    choose g hg using hK'
    have he := sum_coe_sort (degreeIndices n r) (fun a =>
      (mvPolynomialBaseTranslation (1 : Fin n → ℂ) F).coeff a * logMonomial (fun i => (Real.log (p i) : ℂ)) a)
    have hsum' : ∑ b : degreeIndices n r, g b • logMonomial (fun i => (Real.log (p i) : ℂ)) b = 0 := by
      rw [← hsum, ← he]
      refine sum_congr rfl fun b _ => ?_
      rw [Algebra.smul_def, hg]
    have hzero := hind (fun b => g b) hsum'
    rw [mem_pointIdeal_pow_iff_centered_coeff]
    intro a ha
    by_cases heq : Finsupp.degree a = r
    · have := hzero ⟨a, mem_degreeIndices_iff.mpr heq⟩
      rw [← hg a, this, map_zero]
    · exact (mem_pointIdeal_pow_iff_centered_coeff F 1 r).mp hF a (by omega)

/-! ## The unconditional cases -/

/-- The degree-one multi-indices are the coordinates. -/
def degreeOneEquiv (n : ℕ) : Fin n ≃ degreeIndices n 1 :=
  Equiv.ofBijective (fun i => ⟨Finsupp.single i 1, mem_degreeIndices_iff.mpr (by simp)⟩) (by
    constructor
    · intro i j h
      have h' := congrArg Subtype.val h
      exact (Finsupp.single_left_inj (by norm_num)).mp h'
    · rintro ⟨a, ha⟩
      have hd := (mem_finsuppAntidiag.mp ha).1
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hd
      have hd' : ∑ x, a x = 1 := hd
      have hsplit : a i + ∑ x ∈ univ.erase i, a x = ∑ x, a x := Finset.add_sum_erase univ a (mem_univ i)
      have h1 : a i = 1 := by omega
      have hrest : ∑ j ∈ univ.erase i, a j = 0 := by omega
      refine ⟨i, Subtype.ext ?_⟩
      ext j
      by_cases hij : j = i
      · subst hij; simpa using h1.symm
      · have hj := (Finset.sum_eq_zero_iff.mp hrest) j (mem_erase.mpr ⟨hij, mem_univ j⟩)
        simpa [Ne.symm hij] using hj.symm)

/-- **Order one: Baker.** For distinct primes and algebraic coefficients, the first scalar jet recovers all first
mixed jets. -/
theorem sameOrderRecovery_one (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun a : degreeIndices n 1 => logMonomial (fun i => (Real.log (p i) : ℂ)) a) := by
  refine (linearIndependent_equiv (degreeOneEquiv n)).mp ?_
  convert GaloisForLFunctions.RHTower.primeLogs_algClosure_linearIndependent p hp hinj using 1
  funext i
  simp only [Function.comp, degreeOneEquiv, Equiv.ofBijective_apply, logMonomial]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The degree-`T` multi-indices of two coordinates. -/
def degreeTwoEquiv (T : ℕ) : Fin (T + 1) ≃ degreeIndices 2 T :=
  Equiv.ofBijective
    (fun j => ⟨Finsupp.equivFunOnFinite.symm ![j.val, T - j.val], mem_degreeIndices_iff.mpr (by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      have := Nat.le_of_lt_succ j.isLt
      omega)⟩) (by
    constructor
    · intro i j h
      have h' := congrArg (fun a : degreeIndices 2 T => (a : Fin 2 →₀ ℕ) 0) h
      simpa [Fin.ext_iff] using h'
    · rintro ⟨a, ha⟩
      have hd := mem_degreeIndices_iff.mp ha
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
      refine ⟨⟨a 0, by omega⟩, Subtype.ext ?_⟩
      ext i
      fin_cases i
      · simp
      · simp
        omega)

/-- **Two primes: Gelfond–Schneider.** At every order, for two distinct primes and algebraic coefficients, the scalar
jet recovers all mixed jets. -/
theorem sameOrderRecovery_two_primes {P Q : ℕ} (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q) (T : ℕ) :
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun a : degreeIndices 2 T => logMonomial (fun i => (Real.log ((![P, Q] : Fin 2 → ℕ) i) : ℂ)) a) := by
  refine (linearIndependent_equiv (degreeTwoEquiv T)).mp ?_
  convert twoPrimeLog_homogeneous_algClosure_linearIndependent hP hQ hPQ T using 1
  funext j
  simp [Function.comp, degreeTwoEquiv, logMonomial, Fin.prod_univ_two]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iteratedDeriv_primeLogTrace_eq_leadingForm
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sameOrderRecovery_iff_linearIndependent
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sameOrderRecovery_one
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sameOrderRecovery_two_primes
