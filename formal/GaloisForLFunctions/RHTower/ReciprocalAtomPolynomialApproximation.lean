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

/-- The finite set of reciprocal test points of norm at least `r`. -/
def xiCoarseAtoms {r : ℝ} (hr : 0 < r) : Finset ℂ :=
  (finite_xiReciprocalTestSet_norm_ge hr).toFinset

theorem mem_xiCoarseAtoms {r : ℝ} (hr : 0 < r) (z : ℂ) :
    z ∈ xiCoarseAtoms hr ↔ z ∈ xiReciprocalTestSet ∧ r ≤ ‖z‖ := by
  simp [xiCoarseAtoms, Set.Finite.mem_toFinset]

theorem xiCoarseAtoms_conj {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ xiCoarseAtoms hr) :
    (starRingEnd ℂ) z ∈ xiCoarseAtoms hr := by
  rw [mem_xiCoarseAtoms] at hz ⊢
  refine ⟨?_, by simpa using hz.2⟩
  rcases hz.1 with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp [h]))
  · exact xiReciprocalAtomSet_subset (xiReciprocalAtomSet_conj h)

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

/-- **Real polynomials isolate reciprocal atoms.**  Every conjugation-symmetric atom isolator is a
uniform limit on the reciprocal atom set of real polynomials divisible by any prescribed power of
the hard-edge coordinate. -/
theorem exists_realPolynomial_atomIsolator_approx {a ζ : ℂ} (ha : a ∈ xiReciprocalAtomSet)
    (hζ : a = (starRingEnd ℂ) a → ζ = (starRingEnd ℂ) ζ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, (X ^ m ∣ p) ∧
      ∀ z ∈ xiReciprocalAtomSet,
        ‖xiAtomIsolator a ζ z - (Polynomial.aeval z p : ℂ)‖ ≤ ε := by
  classical
  have ha0 : a ≠ 0 := xiReciprocalAtom_ne_zero ha
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set δ : ℝ := ‖a‖ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set S : Finset ℂ := xiCoarseAtoms hδ with hS
  have haF : a ∈ S := by
    rw [hS, mem_xiCoarseAtoms]
    exact ⟨xiReciprocalAtomSet_subset ha, by rw [hδdef]; linarith⟩
  have hcaF : (starRingEnd ℂ) a ∈ S := xiCoarseAtoms_conj hδ haF
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
  -- basic evaluation formulas
  have hPeval : ∀ z : ℂ, P.eval z = ζ' * L.eval z * (a⁻¹ * z) ^ N := by
    intro z; simp [hP]
  have hReval : ∀ z : ℂ, R.eval z = P.eval z + (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
    intro z; rw [hR, Polynomial.eval_add, eval_map_conj]
  have hinj : Set.InjOn id (S : Set ℂ) := fun _ _ _ _ h => h
  have hbasisSelf : L.eval a = 1 := by
    simpa [hL] using Lagrange.eval_basis_self hinj haF
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
  -- the lift to a real polynomial
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
  · -- divisibility
    rw [Polynomial.X_pow_dvd_iff]
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
    have : (algebraMap ℝ ℂ) (q.coeff i) = 0 := by
      rw [← Polynomial.coeff_map, hq, hRi]
    exact (map_eq_zero_iff _ (algebraMap ℝ ℂ).injective).mp this
  · intro z hz
    rw [hqeval, hReval]
    by_cases hzF : z ∈ S
    · have hczF : (starRingEnd ℂ) z ∈ S := xiCoarseAtoms_conj hδ hzF
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
          rw [hPa, hζ'val, hPzero _ hcaF hcane, map_zero, add_zero, sub_self, norm_zero]
          exact hε.le
      · by_cases hzb : z = (starRingEnd ℂ) a
        · have hcane : (starRingEnd ℂ) a ≠ a := by rw [← hzb]; exact hza
          have hζ'val : ζ' = ζ := by
            refine hζ'.trans (if_neg (fun hc => hcane hc.symm))
          have hcz : (starRingEnd ℂ) z = a := by rw [hzb, Complex.conj_conj]
          have hiso : xiAtomIsolator a ζ z = (starRingEnd ℂ) ζ := by
            simp only [xiAtomIsolator, if_neg hza, if_pos hzb]
          rw [hiso, hPzero z hzF hza, hcz, hPa, hζ'val, zero_add, sub_self, norm_zero]
          exact hε.le
        · have hcza : (starRingEnd ℂ) z ≠ a := fun hc => hzb (by rw [← hc, Complex.conj_conj])
          have hiso : xiAtomIsolator a ζ z = 0 := by
            simp only [xiAtomIsolator, if_neg hza, if_neg hzb]
          rw [hiso, hPzero z hzF hza, hPzero _ hczF hcza, map_zero, add_zero, sub_self, norm_zero]
          exact hε.le
    · have hzsmall : ‖z‖ ≤ δ := by
        by_contra hc
        refine hzF ?_
        rw [hS, mem_xiCoarseAtoms]
        exact ⟨xiReciprocalAtomSet_subset hz, le_of_lt (not_le.mp hc)⟩
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

/-! ### Polynomial filters -/

/-- The filtered reciprocal form `Q_h[q] = Q₀[h q]`. -/
def xiFilteredForm (h q : Polynomial ℝ) : ℝ := (xiQZero (xiPolynomialTest (h * q))).re

theorem xiPolynomialTest_mul_atomIsolator {h : Polynomial ℝ} {a ζ : ℂ}
    (hha : xiPolynomialTest h a ≠ 0) (z : ℂ) :
    xiPolynomialTest h z * xiAtomIsolator a (ζ / xiPolynomialTest h a) z =
      xiAtomIsolator a ζ z := by
  unfold xiAtomIsolator
  split_ifs with h1 h2
  · rw [h1]
    field_simp
  · rw [h2]
    have hconj : xiPolynomialTest h ((starRingEnd ℂ) a) =
        (starRingEnd ℂ) (xiPolynomialTest h a) := aeval_conj h a
    rw [hconj, ← map_mul]
    congr 1
    field_simp
  · ring

/-- **A polynomial filter proves RH exactly on the atoms it does not annihilate.** -/
theorem xiFilteredForm_nonneg_iff (h : Polynomial ℝ) :
    (∀ q : Polynomial ℝ, 0 ≤ xiFilteredForm h q) ↔
      ∀ q0 : XiZeroCopy, xiPolynomialTest h (xiZeroCopyReciprocalSquare q0) ≠ 0 →
        (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q0 := by
  obtain ⟨D, hD0, hD⟩ := exists_polynomial_bound_on_atoms h
  constructor
  · intro hpos q0 hvis
    refine xiReciprocalAtom_nonneg_of_isolator q0 (fun ζ hζ => ?_)
    refine xiQZero_re_nonneg_of_uniform_approx (M := ‖ζ‖)
      (fun b _ => xiAtomIsolator_norm_le _ ζ b)
      (Set.range fun q : Polynomial ℝ => xiPolynomialTest (h * q)) ?_ ?_
    · rintro g ⟨q, rfl⟩
      exact hpos q
    · intro ε hε
      set a := xiZeroCopyReciprocalSquare q0 with hadef
      set ζ' : ℂ := ζ / xiPolynomialTest h a with hζ'
      have hζ'symm : a = (starRingEnd ℂ) a → ζ' = (starRingEnd ℂ) ζ' := by
        intro hreal
        have hhreal : xiPolynomialTest h a = (starRingEnd ℂ) (xiPolynomialTest h a) := by
          conv_lhs => rw [hreal]
          exact aeval_conj h a
        rw [hζ', map_div₀, ← hζ hreal, ← hhreal]
      obtain ⟨p, -, hp⟩ := exists_realPolynomial_atomIsolator_approx (a := a) ⟨q0, rfl⟩
        hζ'symm 0 (by positivity : 0 < ε / (D + 1))
      refine ⟨xiPolynomialTest (h * p), ⟨p, rfl⟩, fun b hb => ?_⟩
      rw [xiPolynomialTest_mul, ← xiPolynomialTest_mul_atomIsolator hvis b, ← hζ', ← mul_sub,
        norm_mul]
      have h1 : ‖xiPolynomialTest h b‖ ≤ D := hD b hb
      have h2 : ‖xiAtomIsolator a ζ' b - xiPolynomialTest p b‖ ≤ ε / (D + 1) := hp b hb
      calc ‖xiPolynomialTest h b‖ * ‖xiAtomIsolator a ζ' b - xiPolynomialTest p b‖
          ≤ D * (ε / (D + 1)) :=
            mul_le_mul h1 h2 (norm_nonneg _) hD0
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            nlinarith
  · intro hvis q
    obtain ⟨M, -, hM⟩ := exists_polynomial_bound_on_atoms (h * q)
    have hsum := summable_xiQZeroTerm hM
    rw [xiFilteredForm, xiQZero, Complex.re_tsum hsum]
    refine tsum_nonneg (fun q0 => ?_)
    set a := xiZeroCopyReciprocalSquare q0 with hadef
    by_cases hha : xiPolynomialTest h a = 0
    · have : xiPolynomialTest (h * q) a = 0 := by
        rw [xiPolynomialTest_mul, hha, zero_mul]
      rw [this]
      simp
    · have hnn : (0 : ℂ) ≤ a := hvis q0 hha
      obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
      have hconj : (starRingEnd ℂ) a = a := Complex.conj_eq_iff_im.mpr him.symm
      have hfsymm : xiPolynomialTest (h * q) a =
          (starRingEnd ℂ) (xiPolynomialTest (h * q) a) := by
        conv_lhs => rw [← hconj]
        exact aeval_conj (h * q) a
      have hfim : (xiPolynomialTest (h * q) a).im = 0 :=
        Complex.conj_eq_iff_im.mp hfsymm.symm
      have hsqre : ((xiPolynomialTest (h * q) a) ^ 2).re =
          (xiPolynomialTest (h * q) a).re ^ 2 := by
        rw [pow_two, Complex.mul_re, hfim]; ring
      have hsqim : ((xiPolynomialTest (h * q) a) ^ 2).im = 0 := by
        rw [pow_two, Complex.mul_im, hfim]; ring
      have hmulre : (a * xiPolynomialTest (h * q) a ^ 2).re =
          a.re * (xiPolynomialTest (h * q) a).re ^ 2 := by
        rw [Complex.mul_re, hsqre, hsqim, ← him]
        ring
      rw [hmulre]
      exact mul_nonneg hre (sq_nonneg _)

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

end RHTower
