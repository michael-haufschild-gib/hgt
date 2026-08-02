import GaloisForLFunctions.HTGeometry.LogRatApproximant
import GaloisForLFunctions.HTGeometry.ShiftedJetPolyDatum

/-!
# The boundary datum of the shifted polygamma field

With the logarithm in the model the dichotomy runs on the whole field: a polynomial in the shifted
digamma jets of *every* order, `ψ` itself included, is either negligible or has a boundary datum.
The comparison is against the shape `s^{-N}`, and it is decided by the ordering the shape already
carries: a dominant signature that did not beat `s^{-N}` would make the whole approximant, and hence
the function, negligible at order `N`.

Since the Hölder elimination forbids that for a nonzero polynomial, every nonzero element of the
shifted polygamma ring has an argument exponent, a logarithm exponent and a nonzero residue.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] germRatFuncAlgebra

variable {r : ℕ}

/-- A quantity dominated on the tube by a null one is null. -/
theorem tubeLimit_zero_of_norm_le {M K T₀ : ℝ} {g h : ℝ → ℝ → ℂ} (hg : TubeLimit M g 0)
    (hK : 0 ≤ K) (hb : ∀ σ t : ℝ, 0 < σ → σ ≤ M → T₀ ≤ t → ‖h σ t‖ ≤ K * ‖g σ t‖) :
    TubeLimit M h 0 := by
  intro ε hε
  obtain ⟨T, hT⟩ := hg (ε / (K + 1)) (by positivity)
  refine ⟨max T T₀, fun σ t hσ hσM ht => ?_⟩
  have h1 := hT σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hb σ t hσ hσM (le_trans (le_max_right _ _) ht)
  rw [sub_zero] at h1 ⊢
  have h3 : K * ‖g σ t‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK
  have h4 : K * (ε / (K + 1)) ≤ ε := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The modulus of the boundary shape of a negative integer exponent. -/
theorem norm_shape_neg_natCast (σ : ℝ) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ‖gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t‖ = (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ N)⁻¹ := by
  have hpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
    norm_pos_iff.mpr (vertical_ne_zero_of_pos ht)
  rw [gammaShiftShape, zpow_zero, one_mul, zpow_zero, mul_one, norm_cpow_real_vertical,
    Real.rpow_neg hpos.le, Real.rpow_natCast]

/-- **A function with logarithmic rational approximants is negligible or has a boundary datum.** -/
theorem exists_hasShiftTubeDatum_of_logRatApprox {f : ℂ → ℂ} (hf : HasLogRatApprox f)
    (hnn : ¬ IsVerticallyNegligible f) {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0 (fun σ t => f ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c := by
  classical
  obtain ⟨M₀, N, hM₀, hnot⟩ := exists_not_isTubeBigO hnn
  set M' : ℝ := max M M₀ with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le hM (le_max_left _ _)
  have hMM' : M ≤ M' := le_max_left _ _
  have hnot' : ¬ IsTubeBigO M' N f := fun hb => hnot (hb.mono_tube (le_max_right _ _))
  obtain ⟨A, q, C, T, hq, hC, hT, hb⟩ := hf M' hM'pos N
  have hA : A ≠ 0 := by
    intro h0
    refine hnot' ⟨C, max T 2, fun σ t hσ hσM ht => ?_⟩
    have h := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
    rw [h0] at h
    simpa [logPolyEval] using h
  obtain ⟨k, hk, hdat⟩ := exists_hasShiftTubeDatum_logPolyEval hM'pos hA hq
  set ω : ℝ := ((A.coeff k).natDegree : ℝ) - (q.natDegree : ℝ) with hω
  set b : ℤ := (k : ℤ) with hbdef
  set c : ℂ := (A.coeff k).leadingCoeff / q.leadingCoeff with hc
  -- the dominant signature beats the error order
  have hdom : ShiftShapeDominates 0 ω b 0 (-(N : ℝ)) 0 := by
    by_contra hcon
    have hnot1 : ¬ ((0 : ℤ) = 0 ∧ -(N : ℝ) < ω) := fun h => hcon (Or.inr (Or.inl h))
    have hnot2 : ¬ ((0 : ℤ) = 0 ∧ -(N : ℝ) = ω ∧ (0 : ℤ) < b) :=
      fun h => hcon (Or.inr (Or.inr h))
    have hωle : ω ≤ -(N : ℝ) := by
      by_contra hlt
      exact hnot1 ⟨rfl, by linarith [not_le.mp hlt]⟩
    -- the approximant is then already of the failing order
    have hcmp : ∃ T' : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M' → T' ≤ t →
        ‖gammaShiftShape 0 σ 0 ω b t‖ ≤ ‖gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t‖ := by
      by_cases heq : ω = -(N : ℝ)
      · by_cases hb0 : b = 0
        · exact ⟨2, fun σ t hσ hσM ht => by rw [heq, hb0]⟩
        · have hblt : b < 0 := by
            rcases lt_trichotomy b 0 with h | h | h
            · exact h
            · exact absurd h hb0
            · exact absurd ⟨rfl, heq.symm, h⟩ hnot2
          have hsub : ShiftShapeDominates 0 (-(N : ℝ)) 0 0 ω b :=
            Or.inr (Or.inr ⟨rfl, heq, hblt⟩)
          obtain ⟨T', hT'⟩ := tubeLimit_gammaShiftShape_ratio_zero hM'pos le_rfl hsub 1 one_pos
          refine ⟨max T' 3, fun σ t hσ hσM ht => ?_⟩
          have h1 := hT' σ t hσ hσM (le_trans (le_max_left _ _) ht)
          have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
          have hne : gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t ≠ 0 :=
            gammaShiftShape_ne_zero (by linarith) ht3 _ _ _
          rw [sub_zero, norm_div, div_le_one (by positivity)] at h1
          exact h1
      · have hsub : ShiftShapeDominates 0 (-(N : ℝ)) 0 0 ω b :=
          Or.inr (Or.inl ⟨rfl, lt_of_le_of_ne hωle heq⟩)
        obtain ⟨T', hT'⟩ := tubeLimit_gammaShiftShape_ratio_zero hM'pos le_rfl hsub 1 one_pos
        refine ⟨max T' 3, fun σ t hσ hσM ht => ?_⟩
        have h1 := hT' σ t hσ hσM (le_trans (le_max_left _ _) ht)
        have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
        have hne : gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t ≠ 0 :=
          gammaShiftShape_ne_zero (by linarith) ht3 _ _ _
        rw [sub_zero, norm_div, div_le_one (by positivity)] at h1
        exact h1
    obtain ⟨T', hT'⟩ := hcmp
    obtain ⟨T₂, hT₂⟩ := hdat.2.exists_bound
    refine hnot' ⟨C + (‖c‖ + 1), max (max T T') (max T₂ 3), fun σ t hσ hσM ht => ?_⟩
    have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
    have htpos : (0 : ℝ) < t := by linarith
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have h1 := hb σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
    have h2 := hT' σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
    have h3 := hT₂ σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
    set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
    have hshape : gammaShiftShape 0 σ 0 ω b t ≠ 0 :=
      gammaShiftShape_ne_zero (by linarith) ht3 _ _ _
    have hshapepos : (0 : ℝ) < ‖gammaShiftShape 0 σ 0 ω b t‖ := norm_pos_iff.mpr hshape
    have happrox : ‖logPolyEval A s / Polynomial.eval s q‖
        ≤ (‖c‖ + 1) * ‖gammaShiftShape 0 σ 0 ω b t‖ := by
      simp only [norm_div] at h3
      rw [div_le_iff₀ hshapepos] at h3
      rw [norm_div]
      exact h3
    have hnorm : ‖gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t‖ ≤ (t ^ N)⁻¹ := by
      rw [norm_shape_neg_natCast σ htpos N]
      have hge : t ≤ ‖s‖ := norm_vertical_ge_im σ t
      have hpow : t ^ N ≤ ‖s‖ ^ N := pow_le_pow_left₀ (by positivity) hge N
      exact inv_anti₀ (by positivity) hpow
    have hfin : ‖f s‖ ≤ (C + (‖c‖ + 1)) / t ^ N := by
      have hsplit : ‖f s‖ ≤ ‖f s - logPolyEval A s / Polynomial.eval s q‖
          + ‖logPolyEval A s / Polynomial.eval s q‖ := by
        have := norm_add_le (f s - logPolyEval A s / Polynomial.eval s q)
          (logPolyEval A s / Polynomial.eval s q)
        simpa using this
      have hstep : ‖logPolyEval A s / Polynomial.eval s q‖ ≤ (‖c‖ + 1) / t ^ N := by
        refine le_trans happrox ?_
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left (le_trans (le_trans h2 hnorm) le_rfl) (by positivity)
      have hsum : C / t ^ N + (‖c‖ + 1) / t ^ N = (C + (‖c‖ + 1)) / t ^ N := by ring
      linarith
    exact hfin
  -- the error is negligible against the dominant shape
  have hratio := tubeLimit_gammaShiftShape_ratio_zero hM'pos le_rfl hdom
  have herr : TubeLimit M' (fun σ t =>
      (f ((σ : ℂ) + (t : ℂ) * Complex.I)
        - logPolyEval A ((σ : ℂ) + (t : ℂ) * Complex.I)
          / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q)
      / gammaShiftShape 0 σ 0 ω b t) 0 := by
    refine tubeLimit_zero_of_norm_le (K := C * (1 + M') ^ N) (T₀ := max T 3) hratio
      (by positivity) fun σ t hσ hσM ht => ?_
    have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htpos : (0 : ℝ) < t := by linarith
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have h1 := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
    set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
    have hshape : gammaShiftShape 0 σ 0 ω b t ≠ 0 :=
      gammaShiftShape_ne_zero (by linarith) ht3 _ _ _
    have hsle : ‖s‖ ≤ (1 + M') * t := norm_vertical_le_of_le hσ hσM ht1
    have hspos : (0 : ℝ) < ‖s‖ ^ N := by
      have hs0 : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr (vertical_ne_zero_of_pos htpos)
      positivity
    have hlow : C / t ^ N ≤ C * (1 + M') ^ N * ‖gammaShiftShape 0 σ 0 (-(N : ℝ)) 0 t‖ := by
      rw [norm_shape_neg_natCast σ htpos N, ← div_eq_mul_inv,
        div_le_div_iff₀ (by positivity) hspos]
      calc C * ‖s‖ ^ N ≤ C * ((1 + M') * t) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsle N) hC
        _ = C * (1 + M') ^ N * t ^ N := by rw [mul_pow]; ring
    rw [norm_div, norm_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_trans h1 hlow) (norm_nonneg _)
  have hsum := hdat.2.add herr
  rw [add_zero] at hsum
  have hcast : ((((A.coeff k).natDegree : ℤ) - (q.natDegree : ℤ) : ℤ) : ℝ) = ω := by
    rw [hω]
    push_cast
    ring
  refine ⟨((A.coeff k).natDegree : ℤ) - (q.natDegree : ℤ), b, c, hdat.1, ?_⟩
  rw [hcast]
  refine HasShiftTubeDatum.mono_tube hMM' ⟨hdat.1, ?_⟩
  refine hsum.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hshape : gammaShiftShape 0 σ 0 ω b t ≠ 0 :=
    gammaShiftShape_ne_zero (by linarith) ht _ _ _
  field_simp
  ring

/-- A shifted digamma jet of arbitrary order, as a function. -/
def jetFieldFun (lam : Fin r → ℝ) (pk : Fin r × ℕ) : ℂ → ℂ :=
  fun z => iteratedDeriv pk.2 Complex.digamma (z + ((lam pk.1 : ℝ) : ℂ))

theorem jetFun_eq_jetFieldFun (lam : Fin r → ℝ) (pk : Fin r × ℕ) :
    jetFun lam pk = jetFieldFun lam (pk.1, pk.2 + 1) := rfl

/-- **Every shifted digamma jet is approximable with logarithms.** -/
theorem hasLogRatApprox_jetFieldFun (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (pk : Fin r × ℕ) : HasLogRatApprox (jetFieldFun lam pk) := by
  obtain ⟨i, j⟩ := pk
  cases j with
  | zero =>
      refine (hasLogRatApprox_digamma_shift (hlam i)).congr fun z => ?_
      rw [jetFieldFun, iteratedDeriv_zero]
  | succ n =>
      exact (hasRatApprox_iteratedDeriv_digamma_shift (hlam i) n).hasLogRatApprox

/-- The value of a jet polynomial of the full field with polynomial coefficients. -/
def jetFieldPolyFun (lam : Fin r → ℝ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) : ℂ → ℂ :=
  MvPolynomial.eval₂ polyFunHom (fun k => jetFieldFun lam (idx k)) P

theorem hasLogRatApprox_jetFieldPolyFun (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) {Mm : ℕ}
    (idx : Fin Mm → Fin r × ℕ) (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    HasLogRatApprox (jetFieldPolyFun lam idx P) := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun P => HasLogRatApprox (jetFieldPolyFun lam idx P)) P ?_ ?_ ?_
  · intro a
    refine ((hasRatApprox_polyEval a).hasLogRatApprox).congr fun z => ?_
    simp only [jetFieldPolyFun, MvPolynomial.eval₂_C, polyFunHom_apply]
  · intro p q hp hq
    refine (hp.add hq).congr fun z => ?_
    simp only [jetFieldPolyFun, MvPolynomial.eval₂_add, Pi.add_apply]
  · intro p k hp
    refine (hp.mul (hasLogRatApprox_jetFieldFun lam hlam (idx k))).congr fun z => ?_
    simp only [jetFieldPolyFun, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply]

/-- The value of a jet polynomial of the full field is the germ the eliminator works with. -/
theorem shiftedJetEval_map_eq_coe_field (lam : Fin r → ℝ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    shiftedJetEval lam idx (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P)
      = ((jetFieldPolyFun lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  have hcoe : ((jetFieldPolyFun lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ)
      = MvPolynomial.eval₂ ((Germ.coeRingHom upperEndFilter).comp polyFunHom)
        (fun k => ((jetFieldFun lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ)) P := by
    rw [jetFieldPolyFun]
    exact MvPolynomial.eval₂_comp_left (Germ.coeRingHom upperEndFilter) polyFunHom
      (fun k => jetFieldFun lam (idx k)) P
  have hhom : (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ)).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      = (Germ.coeRingHom upperEndFilter).comp polyFunHom := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      ratFuncGerm_algebraMap, polyGermHom_apply]
    rfl
  have hfun : (fun k => jetGerm lam (idx k))
      = fun k => ((jetFieldFun lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
    funext k
    rw [jetGerm]
    rfl
  rw [hcoe, shiftedJetEval, MvPolynomial.eval₂_map, hhom, hfun]

/-- **Equation (11): the boundary datum of a nonzero element of the shifted polygamma ring.**  For
pairwise incongruent nonnegative shifts, the value of a nonzero polynomial in the shifted digamma
jets of any orders, with polynomial coefficients, has an argument exponent, a logarithm exponent and
a nonzero residue on every vertical tube. -/
theorem exists_hasShiftTubeDatum_jetFieldPolyFun (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetFieldPolyFun lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c := by
  classical
  have hPmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P ≠ 0 := by
    intro h0
    refine hP ?_
    have hmap : Function.Injective
        (MvPolynomial.map (σ := Fin Mm) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
      MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    exact hmap (by rw [h0, map_zero])
  have hgerm := not_isGermNegligible_shiftedJetEval lam hincong idx hinj hPmap
  rw [shiftedJetEval_map_eq_coe_field lam idx P] at hgerm
  have hnn : ¬ IsVerticallyNegligible (jetFieldPolyFun lam idx P) := by
    intro hneg
    exact hgerm (isGermNegligible_coe.mpr hneg)
  exact exists_hasShiftTubeDatum_of_logRatApprox
    (hasLogRatApprox_jetFieldPolyFun lam hlam idx P) hnn hM

end

end GaloisForLFunctions.HTGeometry
