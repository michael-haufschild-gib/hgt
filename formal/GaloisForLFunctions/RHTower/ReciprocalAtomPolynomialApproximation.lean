import GaloisForLFunctions.RHTower.ReciprocalAtomCounterterm

/-!
# Real polynomials isolate reciprocal atoms

The reciprocal test set has only finitely many points outside any disc around the hard edge `0`.
So the atom isolator at `a` is reached by an explicit elementary construction rather than by a
Mergelyan-type theorem: take the Lagrange basis polynomial at `a` over the finite set of test
points of norm at least `‖a‖ / 2`, multiply by `(z / a) ^ N`, and symmetrize the coefficients.  The
Lagrange factor makes the polynomial exact on that finite set, the power factor makes it uniformly
small on the remaining points — all of norm at most `‖a‖ / 2` — and it supplies any prescribed
vanishing order at the hard edge.

Consequences: nonnegativity of `Q₀` on real polynomials is exactly RH; a counterterm vanishing on
the hard-edge ideal `X ^ m R[X]` cannot hide an atom; and a polynomial filter `h` proves RH exactly
on the atoms where `h` does not vanish.
-/

noncomputable section

namespace RHTower

open Complex Polynomial
open scoped ComplexOrder

theorem eval_map_conj (P : Polynomial ℂ) (z : ℂ) :
    (P.map (starRingEnd ℂ)).eval z = (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, hp, hq]
  | monomial n c => simp [Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow]

theorem exists_polynomial_bound (P : Polynomial ℂ) (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, ‖z‖ ≤ δ → ‖P.eval z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) δ).exists_bound_of_continuousOn
    (P.continuous_aeval.continuousOn)
  refine ⟨max B 0, le_max_right _ _, fun z hz => ?_⟩
  refine le_trans ?_ (le_max_left B 0)
  simpa using hB z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)


/-! ### The general isolator approximation -/

/-- **Real polynomials isolate an isolated point of a thin compact set.**  If `K` is conjugation
invariant and has only finitely many points outside every disc around `0`, then every
conjugation-symmetric isolator at a nonzero point of `K` is a uniform limit on `K` of real
polynomials divisible by any prescribed power of the coordinate.

The construction is explicit: the Lagrange basis polynomial at `a` over the finite set of points of
norm at least `‖a‖ / 2` is exact there; multiplying by `(z / a) ^ N` preserves those values, gives
the prescribed vanishing order at `0`, and makes the polynomial uniformly small on the remaining
points; symmetrizing the coefficients makes it real. -/
theorem exists_realPolynomial_isolator_approx_on {K : Set ℂ}
    (hKconj : ∀ z ∈ K, (starRingEnd ℂ) z ∈ K)
    (hKfin : ∀ r : ℝ, 0 < r → {z ∈ K | r ≤ ‖z‖}.Finite)
    {a ζ : ℂ} (haK : a ∈ K) (ha0 : a ≠ 0)
    (hζ : a = (starRingEnd ℂ) a → ζ = (starRingEnd ℂ) ζ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, (X ^ m ∣ p) ∧
      ∀ z ∈ K, ‖xiAtomIsolator a ζ z - (Polynomial.aeval z p : ℂ)‖ ≤ ε := by
  classical
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set δ : ℝ := ‖a‖ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set S : Finset ℂ := (hKfin δ hδ).toFinset with hS
  have hmemS : ∀ z : ℂ, z ∈ S ↔ z ∈ K ∧ δ ≤ ‖z‖ := by
    intro z
    rw [hS, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hSconj : ∀ {z : ℂ}, z ∈ S → (starRingEnd ℂ) z ∈ S := by
    intro z hz
    rw [hmemS] at hz ⊢
    exact ⟨hKconj z hz.1, by simpa using hz.2⟩
  have haS : a ∈ S := by
    rw [hmemS]
    exact ⟨haK, by rw [hδdef]; linarith⟩
  have hcaS : (starRingEnd ℂ) a ∈ S := hSconj haS
  set ζ' : ℂ := if a = (starRingEnd ℂ) a then ζ / 2 else ζ with hζ'
  set L : Polynomial ℂ := Lagrange.basis S id a with hL
  obtain ⟨B, hB0, hB⟩ := exists_polynomial_bound L δ
  obtain ⟨N, hNm, hNb⟩ : ∃ N : ℕ, m ≤ N ∧ ‖ζ'‖ * B * (1 / 2 : ℝ) ^ N ≤ ε / 2 := by
    have h2 : Filter.Tendsto (fun n : ℕ => ‖ζ'‖ * B * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
      simpa using hp.const_mul (‖ζ'‖ * B)
    have h3 : ∀ᶠ n : ℕ in Filter.atTop, ‖ζ'‖ * B * (1 / 2 : ℝ) ^ n ≤ ε / 2 := by
      filter_upwards [h2.eventually_le_const (by positivity : (0 : ℝ) < ε / 2)] with n hn using hn
    obtain ⟨N, hN⟩ := (h3.and (Filter.eventually_ge_atTop m)).exists
    exact ⟨N, hN.2, hN.1⟩
  set P : Polynomial ℂ := Polynomial.C ζ' * L * (Polynomial.C a⁻¹ * X) ^ N with hP
  set R : Polynomial ℂ := P + P.map (starRingEnd ℂ) with hR
  have hPeval : ∀ z : ℂ, P.eval z = ζ' * L.eval z * (a⁻¹ * z) ^ N := by
    intro z; simp [hP]
  have hReval : ∀ z : ℂ, R.eval z = P.eval z + (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
    intro z; rw [hR, Polynomial.eval_add, eval_map_conj]
  have hinj : Set.InjOn id (S : Set ℂ) := fun _ _ _ _ h => h
  have hbasisSelf : L.eval a = 1 := by
    simpa [hL] using Lagrange.eval_basis_self (s := S) (v := (id : ℂ → ℂ)) hinj haS
  have hbasisNe : ∀ w ∈ S, w ≠ a → L.eval w = 0 := by
    intro w hw hwa
    simpa [hL] using
      Lagrange.eval_basis_of_ne (s := S) (v := (id : ℂ → ℂ)) (i := a) (j := w) (Ne.symm hwa) hw
  have hPa : P.eval a = ζ' := by
    rw [hPeval, hbasisSelf, inv_mul_cancel₀ ha0, one_pow]
    ring
  have hPzero : ∀ w ∈ S, w ≠ a → P.eval w = 0 := by
    intro w hw hwa
    rw [hPeval, hbasisNe w hw hwa]
    ring
  have hPsmall : ∀ z : ℂ, ‖z‖ ≤ δ → ‖P.eval z‖ ≤ ε / 2 := by
    intro z hz
    rw [hPeval, norm_mul, norm_mul, norm_pow, norm_mul, norm_inv]
    have hfrac : ‖a‖⁻¹ * ‖z‖ ≤ 1 / 2 := by
      rw [inv_mul_eq_div, div_le_div_iff₀ hna (by norm_num : (0:ℝ) < 2)]
      rw [hδdef] at hz
      linarith
    have hpow : (‖a‖⁻¹ * ‖z‖) ^ N ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) hfrac N
    calc ‖ζ'‖ * ‖L.eval z‖ * (‖a‖⁻¹ * ‖z‖) ^ N
        ≤ ‖ζ'‖ * B * (1 / 2 : ℝ) ^ N := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hB z hz) (norm_nonneg _)) hpow
            (by positivity) (by positivity)
      _ ≤ ε / 2 := hNb
  have hRcoeff : ∀ n : ℕ, (starRingEnd ℂ) (R.coeff n) = R.coeff n := by
    intro n
    rw [hR, Polynomial.coeff_add, Polynomial.coeff_map, map_add, Complex.conj_conj]
    ring
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ, q.map (algebraMap ℝ ℂ) = R := by
    have hlifts : R ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      refine ⟨(R.coeff n).re, ?_⟩
      have him : (R.coeff n).im = 0 := Complex.conj_eq_iff_im.mp (hRcoeff n)
      refine Complex.ext ?_ ?_ <;> simp [him]
    obtain ⟨q, hq⟩ := hlifts
    exact ⟨q, hq⟩
  have hqeval : ∀ z : ℂ, (Polynomial.aeval z q : ℂ) = R.eval z := by
    intro z
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq]
  refine ⟨q, ?_, ?_⟩
  · rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    have hRdvd : (X : Polynomial ℂ) ^ N ∣ R := by
      have h1 : (X : Polynomial ℂ) ^ N ∣ P := by
        rw [hP, mul_pow]
        exact (dvd_mul_left _ _).mul_left _
      exact dvd_add h1 (by
        obtain ⟨g, hg⟩ := h1
        exact ⟨g.map (starRingEnd ℂ), by rw [hg, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X]⟩)
    have hRi : R.coeff i = 0 :=
      (Polynomial.X_pow_dvd_iff.mp hRdvd) i (lt_of_lt_of_le hi hNm)
    have hzero : (algebraMap ℝ ℂ) (q.coeff i) = 0 := by
      rw [← Polynomial.coeff_map, hq, hRi]
    exact (map_eq_zero_iff _ (algebraMap ℝ ℂ).injective).mp hzero
  · intro z hz
    rw [hqeval, hReval]
    by_cases hzS : z ∈ S
    · have hczS : (starRingEnd ℂ) z ∈ S := hSconj hzS
      by_cases hza : z = a
      · rw [hza]
        have hisoa : xiAtomIsolator a ζ a = ζ := by simp [xiAtomIsolator]
        rw [hisoa]
        by_cases hreal : a = (starRingEnd ℂ) a
        · have hζreal : ζ = (starRingEnd ℂ) ζ := hζ hreal
          have hζ'val : ζ' = ζ / 2 := by rw [hζ']; exact if_pos hreal
          have hchalf : (starRingEnd ℂ) (ζ / 2) = ζ / 2 := by
            have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
              apply Complex.ext <;> simp
            rw [map_div₀, h2, ← hζreal]
          rw [← hreal, hPa, hζ'val, hchalf]
          have hzero : ζ - (ζ / 2 + ζ / 2) = 0 := by ring
          rw [hzero, norm_zero]
          exact hε.le
        · have hcane : (starRingEnd ℂ) a ≠ a := fun hc => hreal hc.symm
          have hζ'val : ζ' = ζ := by rw [hζ']; exact if_neg hreal
          rw [hPa, hζ'val, hPzero _ hcaS hcane, map_zero, add_zero, sub_self, norm_zero]
          exact hε.le
      · by_cases hzb : z = (starRingEnd ℂ) a
        · have hcane : (starRingEnd ℂ) a ≠ a := by rw [← hzb]; exact hza
          have hζ'val : ζ' = ζ := hζ'.trans (if_neg (fun hc => hcane hc.symm))
          have hcz : (starRingEnd ℂ) z = a := by rw [hzb, Complex.conj_conj]
          have hiso : xiAtomIsolator a ζ z = (starRingEnd ℂ) ζ := by
            simp only [xiAtomIsolator, if_neg hza, if_pos hzb]
          rw [hiso, hPzero z hzS hza, hcz, hPa, hζ'val, zero_add, sub_self, norm_zero]
          exact hε.le
        · have hcza : (starRingEnd ℂ) z ≠ a := fun hc => hzb (by rw [← hc, Complex.conj_conj])
          have hiso : xiAtomIsolator a ζ z = 0 := by
            simp only [xiAtomIsolator, if_neg hza, if_neg hzb]
          rw [hiso, hPzero z hzS hza, hPzero _ hczS hcza, map_zero, add_zero, sub_self, norm_zero]
          exact hε.le
    · have hzsmall : ‖z‖ ≤ δ := by
        by_contra hc
        exact hzS ((hmemS z).mpr ⟨hz, le_of_lt (not_le.mp hc)⟩)
      have hza : z ≠ a := by
        intro hc
        rw [hc, hδdef] at hzsmall
        linarith
      have hzb : z ≠ (starRingEnd ℂ) a := by
        intro hc
        rw [hc] at hzsmall
        simp only [RCLike.norm_conj] at hzsmall
        rw [hδdef] at hzsmall
        linarith
      have hiso : xiAtomIsolator a ζ z = 0 := by
        simp only [xiAtomIsolator, if_neg hza, if_neg hzb]
      rw [hiso, zero_sub, norm_neg]
      refine le_trans (norm_add_le _ _) ?_
      have h1 := hPsmall z hzsmall
      have h2 : ‖(starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z))‖ ≤ ε / 2 := by
        rw [RCLike.norm_conj]
        exact hPsmall _ (by simpa using hzsmall)
      linarith

theorem xiReciprocalTestSet_conj {z : ℂ} (hz : z ∈ xiReciprocalTestSet) :
    (starRingEnd ℂ) z ∈ xiReciprocalTestSet := by
  rcases hz with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp [h]))
  · exact xiReciprocalAtomSet_subset (xiReciprocalAtomSet_conj h)

/-- **Real polynomials isolate reciprocal atoms.** -/
theorem exists_realPolynomial_atomIsolator_approx {a ζ : ℂ} (ha : a ∈ xiReciprocalAtomSet)
    (hζ : a = (starRingEnd ℂ) a → ζ = (starRingEnd ℂ) ζ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, (X ^ m ∣ p) ∧
      ∀ z ∈ xiReciprocalAtomSet,
        ‖xiAtomIsolator a ζ z - (Polynomial.aeval z p : ℂ)‖ ≤ ε := by
  obtain ⟨p, hdvd, hp⟩ :=
    exists_realPolynomial_isolator_approx_on (K := xiReciprocalTestSet)
      (fun _ hz => xiReciprocalTestSet_conj hz)
      (fun r hr => finite_xiReciprocalTestSet_norm_ge hr)
      (xiReciprocalAtomSet_subset ha) (xiReciprocalAtom_ne_zero ha) hζ m hε
  exact ⟨p, hdvd, fun z hz => hp z (xiReciprocalAtomSet_subset hz)⟩

/-! ### Polynomial test spaces -/

theorem aeval_conj (p : Polynomial ℝ) (z : ℂ) :
    (Polynomial.aeval ((starRingEnd ℂ) z) p : ℂ) =
      (starRingEnd ℂ) (Polynomial.aeval z p : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n c => simp [Polynomial.aeval_monomial, map_mul, map_pow]

theorem exists_norm_bound_xiReciprocalTestSet :
    ∃ M : ℝ, ∀ z ∈ xiReciprocalTestSet, ‖z‖ ≤ M :=
  isBounded_iff_forall_norm_le.mp isCompact_xiReciprocalTestSet.isBounded

/-- The reciprocal test function attached to a real polynomial. -/
def xiPolynomialTest (p : Polynomial ℝ) : ℂ → ℂ := fun z => (Polynomial.aeval z p : ℂ)

theorem xiPolynomialTest_mul (p q : Polynomial ℝ) (z : ℂ) :
    xiPolynomialTest (p * q) z = xiPolynomialTest p z * xiPolynomialTest q z := by
  simp [xiPolynomialTest]

theorem exists_polynomial_bound_on_atoms (p : Polynomial ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ xiReciprocalAtomSet, ‖xiPolynomialTest p z‖ ≤ M := by
  obtain ⟨D, hD⟩ := exists_norm_bound_xiReciprocalTestSet
  obtain ⟨B, hB0, hB⟩ := exists_polynomial_bound (p.map (algebraMap ℝ ℂ)) D
  refine ⟨B, hB0, fun z hz => ?_⟩
  have hev : xiPolynomialTest p z = (p.map (algebraMap ℝ ℂ)).eval z := by
    rw [xiPolynomialTest, Polynomial.aeval_def, Polynomial.eval_map]
  rw [hev]
  exact hB z (hD z (xiReciprocalAtomSet_subset hz))

theorem xiPolynomialTest_isConjSymm (p : Polynomial ℝ) :
    IsConjSymmOn (xiPolynomialTest p) xiReciprocalAtomSet :=
  fun z _ => aeval_conj p z

/-- **The real-polynomial reciprocal test is exactly RH.** -/
theorem riemannHypothesis_iff_forall_polynomial_xiQZero_nonneg :
    RiemannHypothesis ↔ ∀ p : Polynomial ℝ, 0 ≤ (xiQZero (xiPolynomialTest p)).re := by
  constructor
  · intro hRH p
    obtain ⟨M, -, hM⟩ := exists_polynomial_bound_on_atoms p
    exact xiQZero_re_nonneg_of_riemannHypothesis hRH hM (xiPolynomialTest_isConjSymm p)
  · intro hpos
    refine riemannHypothesis_of_visible_all (Set.range xiPolynomialTest) ?_ ?_
    · rintro g ⟨p, rfl⟩
      exact hpos p
    · intro q ζ hζ ε hε
      obtain ⟨p, -, hp⟩ := exists_realPolynomial_atomIsolator_approx ⟨q, rfl⟩ hζ 0 hε
      exact ⟨xiPolynomialTest p, ⟨p, rfl⟩, hp⟩

/-- **Hard-edge counterterms cannot hide an atom.**  A counterterm vanishing on the ideal
`X ^ m R[X]` leaves the repaired polynomial positivity exactly as strong as RH. -/
theorem riemannHypothesis_of_hardEdge_counterterm (m : ℕ) (C : (ℂ → ℂ) → ℝ)
    (hC : ∀ p : Polynomial ℝ, (X : Polynomial ℝ) ^ m ∣ p → C (xiPolynomialTest p) = 0)
    (hpos : ∀ p : Polynomial ℝ, 0 ≤ xiRepairedForm C (xiPolynomialTest p)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_visible_all
    {f | ∃ p : Polynomial ℝ, (X : Polynomial ℝ) ^ m ∣ p ∧ f = xiPolynomialTest p} ?_ ?_
  · rintro g ⟨p, hdvd, rfl⟩
    have hg := hpos p
    rwa [xiRepairedForm, hC p hdvd, add_zero] at hg
  · intro q ζ hζ ε hε
    obtain ⟨p, hdvd, hp⟩ := exists_realPolynomial_atomIsolator_approx ⟨q, rfl⟩ hζ m hε
    exact ⟨xiPolynomialTest p, ⟨p, hdvd, rfl⟩, hp⟩

/-! ### Preconditioners and polynomial filters -/

/-- The preconditioned reciprocal form `Q_g[q] = ∑ M_y y g(y)² q(y)²`. -/
def xiPreconditionedForm (g : ℂ → ℂ) (q : Polynomial ℝ) : ℝ :=
  (xiQZero fun z => g z * xiPolynomialTest q z).re

theorem xiPreconditioner_mul_atomIsolator {g : ℂ → ℂ} {a ζ : ℂ}
    (ha : a ∈ xiReciprocalAtomSet) (hsymm : IsConjSymmOn g xiReciprocalAtomSet)
    (hga : g a ≠ 0) (z : ℂ) :
    g z * xiAtomIsolator a (ζ / g a) z = xiAtomIsolator a ζ z := by
  unfold xiAtomIsolator
  split_ifs with h1 h2
  · rw [h1]
    field_simp
  · rw [h2, hsymm a ha, ← map_mul]
    congr 1
    field_simp
  · ring

/-- **A bounded conjugation-symmetric preconditioner proves RH exactly on the atoms it does not
annihilate.** -/
theorem xiPreconditionedForm_nonneg_iff {g : ℂ → ℂ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ a ∈ xiReciprocalAtomSet, ‖g a‖ ≤ D)
    (hsymm : IsConjSymmOn g xiReciprocalAtomSet) :
    (∀ q : Polynomial ℝ, 0 ≤ xiPreconditionedForm g q) ↔
      ∀ q0 : XiZeroCopy, g (xiZeroCopyReciprocalSquare q0) ≠ 0 →
        (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q0 := by
  constructor
  · intro hpos q0 hvis
    refine xiReciprocalAtom_nonneg_of_isolator q0 (fun ζ hζ => ?_)
    refine xiQZero_re_nonneg_of_uniform_approx (M := ‖ζ‖)
      (fun b _ => xiAtomIsolator_norm_le _ ζ b)
      (Set.range fun q : Polynomial ℝ => fun z => g z * xiPolynomialTest q z) ?_ ?_
    · rintro f ⟨q, rfl⟩
      exact hpos q
    · intro ε hε
      set a := xiZeroCopyReciprocalSquare q0 with hadef
      have haAtom : a ∈ xiReciprocalAtomSet := ⟨q0, rfl⟩
      set ζ' : ℂ := ζ / g a with hζ'
      have hζ'symm : a = (starRingEnd ℂ) a → ζ' = (starRingEnd ℂ) ζ' := by
        intro hreal
        have hgreal : g a = (starRingEnd ℂ) (g a) := by
          conv_lhs => rw [hreal]
          exact hsymm a haAtom
        rw [hζ', map_div₀, ← hζ hreal, ← hgreal]
      obtain ⟨p, -, hp⟩ := exists_realPolynomial_atomIsolator_approx (a := a) haAtom
        hζ'symm 0 (by positivity : 0 < ε / (D + 1))
      refine ⟨fun z => g z * xiPolynomialTest p z, ⟨p, rfl⟩, fun b hb => ?_⟩
      rw [← xiPreconditioner_mul_atomIsolator haAtom hsymm hvis b, ← hζ', ← mul_sub, norm_mul]
      have h1 : ‖g b‖ ≤ D := hD b hb
      have h2 : ‖xiAtomIsolator a ζ' b - xiPolynomialTest p b‖ ≤ ε / (D + 1) := hp b hb
      calc ‖g b‖ * ‖xiAtomIsolator a ζ' b - xiPolynomialTest p b‖
          ≤ D * (ε / (D + 1)) := mul_le_mul h1 h2 (norm_nonneg _) hD0
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            nlinarith
  · intro hvis q
    obtain ⟨Mq, hMq0, hMq⟩ := exists_polynomial_bound_on_atoms q
    have hM : ∀ a ∈ xiReciprocalAtomSet, ‖g a * xiPolynomialTest q a‖ ≤ D * Mq := by
      intro a ha
      rw [norm_mul]
      exact mul_le_mul (hD a ha) (hMq a ha) (norm_nonneg _) hD0
    have hsum := summable_xiQZeroTerm hM
    rw [xiPreconditionedForm, xiQZero, Complex.re_tsum hsum]
    refine tsum_nonneg (fun q0 => ?_)
    set a := xiZeroCopyReciprocalSquare q0 with hadef
    have haAtom : a ∈ xiReciprocalAtomSet := ⟨q0, rfl⟩
    by_cases hga : g a = 0
    · rw [hga, zero_mul]
      simp
    · have hnn : (0 : ℂ) ≤ a := hvis q0 hga
      obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
      have hconj : (starRingEnd ℂ) a = a := Complex.conj_eq_iff_im.mpr him.symm
      have hgim : (g a).im = 0 := by
        refine Complex.conj_eq_iff_im.mp ?_
        conv_rhs => rw [← hconj]
        exact (hsymm a haAtom).symm
      have hqim : (xiPolynomialTest q a).im = 0 := by
        refine Complex.conj_eq_iff_im.mp ?_
        conv_rhs => rw [← hconj]
        exact (aeval_conj q a).symm
      have hfim : (g a * xiPolynomialTest q a).im = 0 := by
        rw [Complex.mul_im, hgim, hqim]; ring
      set w := g a * xiPolynomialTest q a with hw
      have hsqre : (w ^ 2).re = w.re ^ 2 := by rw [pow_two, Complex.mul_re, hfim]; ring
      have hsqim : (w ^ 2).im = 0 := by rw [pow_two, Complex.mul_im, hfim]; ring
      have hmulre : (a * w ^ 2).re = a.re * w.re ^ 2 := by
        rw [Complex.mul_re, hsqre, hsqim, ← him]
        ring
      rw [hmulre]
      exact mul_nonneg hre (sq_nonneg _)

/-- The filtered reciprocal form `Q_h[q] = Q₀[h q]`. -/
def xiFilteredForm (h q : Polynomial ℝ) : ℝ := (xiQZero (xiPolynomialTest (h * q))).re

theorem xiFilteredForm_eq_preconditioned (h q : Polynomial ℝ) :
    xiFilteredForm h q = xiPreconditionedForm (xiPolynomialTest h) q := by
  rw [xiFilteredForm, xiPreconditionedForm]
  congr 1
  exact congrArg _ (funext fun z => xiPolynomialTest_mul h q z)

/-- **A polynomial filter proves RH exactly on the atoms it does not annihilate.** -/
theorem xiFilteredForm_nonneg_iff (h : Polynomial ℝ) :
    (∀ q : Polynomial ℝ, 0 ≤ xiFilteredForm h q) ↔
      ∀ q0 : XiZeroCopy, xiPolynomialTest h (xiZeroCopyReciprocalSquare q0) ≠ 0 →
        (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q0 := by
  obtain ⟨D, hD0, hD⟩ := exists_polynomial_bound_on_atoms h
  have := xiPreconditionedForm_nonneg_iff hD0 hD (xiPolynomialTest_isConjSymm h)
  simpa only [xiFilteredForm_eq_preconditioned] using this

/-- **Finite boundary ideals do not soften the all-order test.** -/
theorem xiFilteredForm_nonneg_iff_riemannHypothesis {h : Polynomial ℝ}
    (hne : ∀ q0 : XiZeroCopy, xiPolynomialTest h (xiZeroCopyReciprocalSquare q0) ≠ 0) :
    (∀ q : Polynomial ℝ, 0 ≤ xiFilteredForm h q) ↔ RiemannHypothesis := by
  rw [xiFilteredForm_nonneg_iff,
    riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative]
  exact ⟨fun hh q0 => hh q0 (hne q0), fun hh q0 _ => hh q0⟩

/-- **Finite exterior boundary conditions are an RH-equivalent chart.** -/
theorem xiBoundaryIdeal_nonneg_iff_riemannHypothesis (B : Finset ℝ)
    (hB : ∀ b ∈ B, ((b : ℝ) : ℂ) ∉ xiReciprocalAtomSet) :
    (∀ q : Polynomial ℝ,
        0 ≤ xiFilteredForm (∏ b ∈ B, (X - Polynomial.C b)) q) ↔ RiemannHypothesis := by
  refine xiFilteredForm_nonneg_iff_riemannHypothesis (fun q0 => ?_)
  have hval : xiPolynomialTest (∏ b ∈ B, (X - Polynomial.C b))
      (xiZeroCopyReciprocalSquare q0) =
      ∏ b ∈ B, (xiZeroCopyReciprocalSquare q0 - ((b : ℝ) : ℂ)) := by
    rw [xiPolynomialTest, map_prod]
    exact Finset.prod_congr rfl (fun b _ => by simp)
  rw [hval, Finset.prod_ne_zero_iff]
  intro b hb
  refine sub_ne_zero.mpr (fun hc => hB b hb ?_)
  rw [← hc]
  exact ⟨q0, rfl⟩

/-! ### The shifted moment tower -/

/-- The shifted reciprocal moment `T_{k+1} = ∑ M_y y^{k+1}`. -/
def xiReciprocalMoment (k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (k + 1)

/-- **The reciprocal form is the shifted moment Hankel form.**  For a real polynomial with
coefficients `c`, `Q₀[p] = ∑_{i,j} c_i c_j T_{i+j+1}`. -/
theorem xiQZero_polynomialTest_eq_hankel (p : Polynomial ℝ) :
    xiQZero (xiPolynomialTest p) =
      ∑ i ∈ Finset.range (p.natDegree + 1), ∑ j ∈ Finset.range (p.natDegree + 1),
        ((p.coeff i : ℂ) * (p.coeff j : ℂ)) * xiReciprocalMoment (i + j) := by
  have hterm : ∀ q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q * xiPolynomialTest p (xiZeroCopyReciprocalSquare q) ^ 2 =
        ∑ ij ∈ (Finset.range (p.natDegree + 1)) ×ˢ (Finset.range (p.natDegree + 1)),
          ((p.coeff ij.1 : ℂ) * (p.coeff ij.2 : ℂ)) *
            xiZeroCopyReciprocalSquare q ^ (ij.1 + ij.2 + 1) := by
    intro q
    have hev : xiPolynomialTest p (xiZeroCopyReciprocalSquare q) =
        ∑ i ∈ Finset.range (p.natDegree + 1),
          (p.coeff i : ℂ) * xiZeroCopyReciprocalSquare q ^ i := by
      rw [xiPolynomialTest, Polynomial.aeval_eq_sum_range]
      exact Finset.sum_congr rfl (fun i _ => by
        simp [Algebra.smul_def])
    rw [Finset.sum_product, hev, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add, pow_succ]
    ring
  have hs : ∀ ij : ℕ × ℕ, Summable fun q : XiZeroCopy =>
      ((p.coeff ij.1 : ℂ) * (p.coeff ij.2 : ℂ)) *
        xiZeroCopyReciprocalSquare q ^ (ij.1 + ij.2 + 1) :=
    fun ij => (summable_xiZeroCopyReciprocalSquare_pow (ij.1 + ij.2)).mul_left _
  rw [xiQZero, tsum_congr hterm, Summable.tsum_finsetSum (fun ij _ => hs ij),
    Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [xiReciprocalMoment, tsum_mul_left]

/-- **The one-point boundary-kernel pre-gate.**  For a real point off the reciprocal support,
all-order positivity on the ideal of polynomials vanishing there is equivalent to RH. -/
theorem xiOnePointBoundary_nonneg_iff_riemannHypothesis {b : ℝ}
    (hb : ((b : ℝ) : ℂ) ∉ xiReciprocalAtomSet) :
    (∀ q : Polynomial ℝ, 0 ≤ xiFilteredForm (X - Polynomial.C b) q) ↔ RiemannHypothesis := by
  refine xiFilteredForm_nonneg_iff_riemannHypothesis (fun q0 => ?_)
  have hval : xiPolynomialTest (X - Polynomial.C b) (xiZeroCopyReciprocalSquare q0) =
      xiZeroCopyReciprocalSquare q0 - ((b : ℝ) : ℂ) := by
    simp [xiPolynomialTest]
  rw [hval]
  refine sub_ne_zero.mpr (fun hc => hb ?_)
  rw [← hc]
  exact ⟨q0, rfl⟩

/-- The first trivial-zero reciprocal coordinate is not a reciprocal atom: it would force a real
`xi` zero at `3` or `-2`, outside the critical strip. -/
theorem xiReciprocalAtomSet_notMem_firstTrivial :
    ((-4 / 25 : ℝ) : ℂ) ∉ xiReciprocalAtomSet := by
  rintro ⟨q, hq⟩
  have hcast : ((-4 / 25 : ℝ) : ℂ) = -4 / 25 := by push_cast; ring
  rw [hcast, xiZeroCopyReciprocalSquare, inv_pow] at hq
  have hsq : (xiSpectralPoint q) ^ 2 = -25 / 4 := by
    have hinv := congrArg (fun w : ℂ => w⁻¹) hq
    simp only [inv_inv] at hinv
    rw [hinv]
    norm_num
  set w : ℂ := ((q.1 : ℂ) - 1 / 2) with hwdef
  have hspw : xiSpectralPoint q = w * (-Complex.I) := rfl
  have hI : ((-Complex.I) ^ 2 : ℂ) = -1 := by
    rw [neg_pow, Complex.I_sq]
    norm_num
  have hw2 : w ^ 2 = 25 / 4 := by
    rw [hspw, mul_pow, hI] at hsq
    linear_combination -hsq
  have hfac : (w - 5 / 2) * (w + 5 / 2) = 0 := by linear_combination hw2
  have hwre : w.re = (q.1 : ℂ).re - 1 / 2 := by
    rw [hwdef]
    simp
  have hcontra : ((q.1 : ℂ).re - 1 / 2) ^ 2 = 25 / 4 := by
    rcases mul_eq_zero.mp hfac with h | h
    · have hval : w = 5 / 2 := by linear_combination h
      rw [← hwre, hval]
      norm_num
    · have hval : w = -(5 / 2) := by linear_combination h
      rw [← hwre, hval]
      norm_num
  have hstrip := xi_divisor_support_centered_re_sq_lt_quarter q.1
  rw [hcontra] at hstrip
  norm_num at hstrip

/-- **The first-trivial-zero Uvarov kernel pre-gate is equivalent to RH.** -/
theorem xiUvarovKernel_nonneg_iff_riemannHypothesis :
    (∀ q : Polynomial ℝ,
        0 ≤ xiFilteredForm (X - Polynomial.C (-4 / 25 : ℝ)) q) ↔ RiemannHypothesis :=
  xiOnePointBoundary_nonneg_iff_riemannHypothesis xiReciprocalAtomSet_notMem_firstTrivial

/-- **Finite exterior boundary channels are RH-strength.**  A repair whose channels are evaluations
at finitely many real points off the reciprocal support vanishes on the corresponding boundary
ideal, and positivity on that ideal is already equivalent to RH. -/
theorem riemannHypothesis_of_finiteBoundaryChannel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (hb : ∀ i, ((b i : ℝ) : ℂ) ∉ xiReciprocalAtomSet)
    (Cq : QuadraticForm ℝ (ι → ℝ))
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (xiQZero (xiPolynomialTest p)).re + Cq (fun i => p.eval (b i))) :
    RiemannHypothesis := by
  classical
  set h : Polynomial ℝ := ∏ i : ι, (X - Polynomial.C (b i)) with hh
  have hzero : ∀ (q : Polynomial ℝ) (i : ι), (h * q).eval (b i) = 0 := by
    intro q i
    rw [Polynomial.eval_mul, hh, Polynomial.eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) ?_) _
    simp
  have hfilt : ∀ q : Polynomial ℝ, 0 ≤ xiFilteredForm h q := by
    intro q
    have hq := hpos (h * q)
    have hC : Cq (fun i => (h * q).eval (b i)) = 0 := by
      have heq : (fun i => (h * q).eval (b i)) = (0 : ι → ℝ) := funext (hzero q)
      rw [heq]
      simp
    rw [hC, add_zero] at hq
    exact hq
  refine (xiFilteredForm_nonneg_iff_riemannHypothesis (fun q0 => ?_)).mp hfilt
  have hval : xiPolynomialTest h (xiZeroCopyReciprocalSquare q0) =
      ∏ i : ι, (xiZeroCopyReciprocalSquare q0 - ((b i : ℝ) : ℂ)) := by
    rw [xiPolynomialTest, hh, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by simp)
  rw [hval, Finset.prod_ne_zero_iff]
  intro i _
  refine sub_ne_zero.mpr (fun hc => hb i ?_)
  rw [← hc]
  exact ⟨q0, rfl⟩

/-! ### Summable exterior boundary measures -/

/-- Positivity with vanishing slack still passes to uniform limits. -/
theorem xiQZero_re_nonneg_of_slack_approx {f : ℂ → ℂ} {M : ℝ}
    (hMf : ∀ a ∈ xiReciprocalAtomSet, ‖f a‖ ≤ M)
    (happrox : ∀ ε > 0, ∃ g : ℂ → ℂ,
      (∀ a ∈ xiReciprocalAtomSet, ‖f a - g a‖ ≤ ε) ∧ -ε ≤ (xiQZero g).re) :
    0 ≤ (xiQZero f).re := by
  obtain ⟨a₀, ha₀⟩ := xiReciprocalAtomSet_nonempty
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMf a₀ ha₀)
  by_contra hcon
  push Not at hcon
  set δ : ℝ := -(xiQZero f).re with hδ
  have hδpos : 0 < δ := by simpa [hδ] using hcon
  set c : ℝ := (2 * M + 1) * xiReciprocalMass with hc
  have hc0 : 0 ≤ c := by
    have h1 : (0:ℝ) ≤ 2 * M + 1 := by linarith
    exact mul_nonneg h1 xiReciprocalMass_nonneg
  set ε : ℝ := min 1 (δ / (2 * (c + 1))) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos hδpos (by linarith))
  have hεle : ε ≤ 1 := min_le_left _ _
  obtain ⟨g, hgapp, hgpos⟩ := happrox ε hεpos
  have hgbdd : ∀ a ∈ xiReciprocalAtomSet, ‖g a‖ ≤ M + ε := by
    intro a ha
    have h1 := hgapp a ha
    have h2 : ‖g a‖ - ‖f a‖ ≤ ‖g a - f a‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h2
    have h3 := hMf a ha
    linarith
  have hbound := norm_xiQZero_sub_le hεpos.le hMf hgbdd hgapp
  have hcε : (M + (M + ε)) * ε * xiReciprocalMass ≤ c * ε := by
    have h1 : M + (M + ε) ≤ 2 * M + 1 := by linarith
    have h2 : (M + (M + ε)) * ε ≤ (2 * M + 1) * ε :=
      mul_le_mul_of_nonneg_right h1 hεpos.le
    calc (M + (M + ε)) * ε * xiReciprocalMass
        ≤ (2 * M + 1) * ε * xiReciprocalMass :=
          mul_le_mul_of_nonneg_right h2 xiReciprocalMass_nonneg
      _ = c * ε := by rw [hc]; ring
  have hfinal : (1 + c) * ε < δ := by
    have hle : ε ≤ δ / (2 * (c + 1)) := min_le_right _ _
    have hstep : (1 + c) * ε ≤ (1 + c) * (δ / (2 * (c + 1))) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    have hfrac : (1 + c) * (δ / (2 * (c + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hre : -‖xiQZero f - xiQZero g‖ ≤ (xiQZero f - xiQZero g).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hsplit : (xiQZero f - xiQZero g).re = (xiQZero f).re - (xiQZero g).re := by
    simp [Complex.sub_re]
  rw [hsplit] at hre
  have hlt : δ < δ := by
    calc δ = -(xiQZero f).re := hδ
      _ ≤ -((xiQZero g).re - ‖xiQZero f - xiQZero g‖) := by linarith
      _ ≤ ε + ‖xiQZero f - xiQZero g‖ := by linarith
      _ ≤ ε + (M + (M + ε)) * ε * xiReciprocalMass := by linarith
      _ ≤ ε + c * ε := by linarith
      _ = (1 + c) * ε := by ring
      _ < δ := hfinal
  exact lt_irrefl δ hlt

/-- **Summable exterior boundary measures are RH-strength.**  A finite-total-variation boundary
measure supported away from the reciprocal atoms cannot hide an off-line atom. -/
theorem riemannHypothesis_of_summableBoundaryMeasure {ι : Type*} (b : ι → ℝ) (β : ι → ℝ)
    (hβ : Summable fun i => |β i|)
    (hb : ∀ i, ((b i : ℝ) : ℂ) ∉ xiReciprocalAtomSet)
    (hbfin : ∀ r : ℝ, 0 < r → {i | r ≤ |b i|}.Finite)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (xiQZero (xiPolynomialTest p)).re + ∑' i, β i * (p.eval (b i)) ^ 2) :
    RiemannHypothesis := by
  classical
  set T : ℝ := ∑' i, |β i| with hT
  have hT0 : 0 ≤ T := tsum_nonneg (fun i => abs_nonneg _)
  set K : Set ℂ := xiReciprocalTestSet ∪ Set.range (fun i => ((b i : ℝ) : ℂ)) with hK
  have hKconj : ∀ z ∈ K, (starRingEnd ℂ) z ∈ K := by
    rintro z (hz | ⟨i, rfl⟩)
    · exact Or.inl (xiReciprocalTestSet_conj hz)
    · exact Or.inr ⟨i, by simp⟩
  have hKfin : ∀ r : ℝ, 0 < r → {z ∈ K | r ≤ ‖z‖}.Finite := by
    intro r hr
    have h1 := finite_xiReciprocalTestSet_norm_ge hr
    have h2 : ((fun i => ((b i : ℝ) : ℂ)) '' {i | r ≤ |b i|}).Finite := (hbfin r hr).image _
    refine (h1.union h2).subset ?_
    rintro z ⟨hzK, hzr⟩
    rcases hzK with hz | ⟨i, rfl⟩
    · exact Or.inl ⟨hz, hzr⟩
    · refine Or.inr ⟨i, ?_, rfl⟩
      simpa [Complex.norm_real] using hzr
  refine riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.mpr (fun q0 => ?_)
  refine xiReciprocalAtom_nonneg_of_isolator q0 (fun ζ hζ => ?_)
  set a := xiZeroCopyReciprocalSquare q0 with hadef
  have haAtom : a ∈ xiReciprocalAtomSet := ⟨q0, rfl⟩
  have haK : a ∈ K := Or.inl (xiReciprocalAtomSet_subset haAtom)
  have ha0 : a ≠ 0 := xiReciprocalAtom_ne_zero haAtom
  have hisoB : ∀ i : ι, xiAtomIsolator a ζ ((b i : ℝ) : ℂ) = 0 := by
    intro i
    have h1 : ((b i : ℝ) : ℂ) ≠ a := fun hc => hb i (by rw [hc]; exact haAtom)
    have h2 : ((b i : ℝ) : ℂ) ≠ (starRingEnd ℂ) a := fun hc =>
      hb i (by rw [hc]; exact xiReciprocalAtomSet_conj haAtom)
    simp only [xiAtomIsolator, if_neg h1, if_neg h2]
  refine xiQZero_re_nonneg_of_slack_approx (M := ‖ζ‖)
    (fun z _ => xiAtomIsolator_norm_le _ ζ z) (fun ε hε => ?_)
  set ε' : ℝ := min (min ε 1) (ε / (T + 1)) with hε'
  have hε'pos : 0 < ε' :=
    lt_min (lt_min hε one_pos) (div_pos hε (by linarith))
  have hε'le : ε' ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'one : ε' ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε'T : ε' ≤ ε / (T + 1) := min_le_right _ _
  obtain ⟨p, -, hp⟩ := exists_realPolynomial_isolator_approx_on hKconj hKfin haK ha0 hζ 0 hε'pos
  refine ⟨xiPolynomialTest p, fun z hz => le_trans (hp z (Or.inl (xiReciprocalAtomSet_subset hz)))
    hε'le, ?_⟩
  have hpB : ∀ i : ι, |p.eval (b i)| ≤ ε' := by
    intro i
    have hz : ((b i : ℝ) : ℂ) ∈ K := Or.inr ⟨i, rfl⟩
    have h1 := hp _ hz
    rw [hisoB i, zero_sub, norm_neg] at h1
    have h2 : (Polynomial.aeval (((b i : ℝ) : ℂ)) p : ℂ) = ((p.eval (b i) : ℝ) : ℂ) := by
      rw [show (((b i : ℝ)) : ℂ) = algebraMap ℝ ℂ (b i) from rfl,
        Polynomial.aeval_algebraMap_apply]
      simp
    rw [h2] at h1
    simpa [Complex.norm_real] using h1
  have hsummable : Summable fun i => β i * (p.eval (b i)) ^ 2 := by
    refine Summable.of_norm_bounded (hβ.mul_right (ε' ^ 2)) (fun i => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hpB i) 2
  have hbnd : ‖∑' i, β i * (p.eval (b i)) ^ 2‖ ≤ T * ε' ^ 2 := by
    refine tsum_of_norm_bounded (g := fun i => |β i| * ε' ^ 2)
      ((hβ.hasSum.mul_right (ε' ^ 2)).congr_fun (fun i => rfl)) (fun i => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hpB i) 2
  have hTε : T * ε' ^ 2 ≤ ε := by
    have h1 : T * ε' ^ 2 ≤ T * (ε / (T + 1)) * ε' := by
      rw [pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε'T hT0) hε'pos.le
    have h2 : T * (ε / (T + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith [hε'pos.le, hε'one, hε.le]
  have hslack : -ε ≤ (xiQZero (xiPolynomialTest p)).re := by
    have h1 := hpos p
    have h2 : -(T * ε' ^ 2) ≤ ∑' i, β i * (p.eval (b i)) ^ 2 := by
      have := abs_le.mp (by simpa [Real.norm_eq_abs] using hbnd)
      linarith [this.1]
    have h3 : ∑' i, β i * (p.eval (b i)) ^ 2 ≤ T * ε' ^ 2 := by
      have := abs_le.mp (by simpa [Real.norm_eq_abs] using hbnd)
      linarith [this.2]
    linarith
  exact hslack

/-- **Finite exterior boundary channels: the full equivalence for a positive channel form.** -/
theorem riemannHypothesis_iff_finiteBoundaryChannel_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (hb : ∀ i, ((b i : ℝ) : ℂ) ∉ xiReciprocalAtomSet)
    (Cq : QuadraticForm ℝ (ι → ℝ)) (hCq : ∀ v : ι → ℝ, 0 ≤ Cq v) :
    (∀ p : Polynomial ℝ,
        0 ≤ (xiQZero (xiPolynomialTest p)).re + Cq (fun i => p.eval (b i))) ↔
      RiemannHypothesis := by
  refine ⟨riemannHypothesis_of_finiteBoundaryChannel b hb Cq, fun hRH p => ?_⟩
  have h1 : 0 ≤ (xiQZero (xiPolynomialTest p)).re :=
    riemannHypothesis_iff_forall_polynomial_xiQZero_nonneg.mp hRH p
  linarith [hCq (fun i => p.eval (b i))]

/-- **Summable exterior boundary measures: the converse for a nonnegative measure.** -/
theorem summableBoundaryMeasure_nonneg_of_riemannHypothesis {ι : Type*} (b : ι → ℝ) (β : ι → ℝ)
    (hβ0 : ∀ i, 0 ≤ β i) (hRH : RiemannHypothesis) (p : Polynomial ℝ) :
    0 ≤ (xiQZero (xiPolynomialTest p)).re + ∑' i, β i * (p.eval (b i)) ^ 2 := by
  have h1 : 0 ≤ (xiQZero (xiPolynomialTest p)).re :=
    riemannHypothesis_iff_forall_polynomial_xiQZero_nonneg.mp hRH p
  have h2 : 0 ≤ ∑' i, β i * (p.eval (b i)) ^ 2 :=
    tsum_nonneg (fun i => mul_nonneg (hβ0 i) (sq_nonneg _))
  linarith

end RHTower
