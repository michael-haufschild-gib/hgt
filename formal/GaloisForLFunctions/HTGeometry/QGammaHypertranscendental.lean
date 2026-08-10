import GaloisForLFunctions.HTGeometry.QDigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.ShiftEigenrelationEngine
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental

/-!
# Pastro's q-analogue of Hölder's theorem

Jackson's q-Gamma function satisfies no algebraic differential equation over `ℂ[z]` on the
half-plane `Re z > 0`.

The proof transfers the algebraic independence of the q-digamma jets through the Bell
substitution.  A differential polynomial for `Γ_q` becomes, after `Γ_q⁽ᵏ⁾ = Γ_q·B_k(ψ_q-jets)`, a
`Γ_q`-power relation `Σ_d Γ_q^d·Q_d(z, qᶻ, ψ_q-jets) = 0`.  The relation is eliminated by induction
on the `Γ_q`-degree against the shift `z ↦ z+1`: Jackson's functional equation
`Γ_q(z+1) = ((1−qᶻ)/(1−q))·Γ_q(z)` contributes the factor `Mᵏ` in degree `k`, the jets transform by
the jet substitution, and cross-multiplying kills the top degree.  The eliminated relation either
terminates in a single term — killed by the algebraic independence of the jets — or in a difference
eigenrelation `σ(f)·g = Mᵉ·f·σ(g)`, refuted by the `u`-degree obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxSynthPendingDepth 4

open MvPolynomial GaloisForLFunctions GaloisForLFunctions.GenericShiftHolder

noncomputable section

/-! ## The integral multiplier -/

/-- Jackson's multiplier `(1 − u)/(1 − q)` inside `ℂ[z][u]`. -/
def qMultInt (q : RealEulerNome) : Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C ((((1 - q.val : ℝ) : ℂ))⁻¹)) * (1 - Polynomial.X)

theorem toQField_qMultInt (q : RealEulerNome) : toQField (qMultInt q) = qMult q := by
  rw [qMultInt, qMult, qMultPoly, toQField_apply, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, algebraMap_polyC, qOneSub,
    ← map_inv₀]

theorem qCoeffEval_qMultInt (q : RealEulerNome) (z : ℂ) :
    qCoeffEval q z (qMultInt q)
      = (1 - (q.val : ℂ) ^ z) / ((1 - q.val : ℝ) : ℂ) := by
  rw [qMultInt, map_mul, qCoeffEval_C, qCoeffEval_one_sub_X, Polynomial.eval_C, qPoint,
    div_eq_inv_mul]

/-! ## The Bell substitution for the q-Gamma function -/

theorem qGamma_iteratedDeriv_eq_bellAt (q : RealEulerNome) {n : ℕ} (k : ℕ) (h : k ≤ n + 1)
    {z : ℂ} (hz : z ∈ qHalfPlane) :
    iteratedDeriv k (qGammaOn q) z
      = qGammaOn q z * eval (qDigammaJet q (n + 1) z) (bellAt n k h) := by
  rw [bellAt, eval_rename]
  rw [qGamma_iteratedDeriv_eq_bellCore q k z hz]
  congr 1

theorem qPolyJetEval_map_C (q : RealEulerNome) (m : ℕ) (z : ℂ)
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) :
    qPolyJetEval q m z (MvPolynomial.map Polynomial.C G)
      = eval₂ (Polynomial.evalRingHom z) (qDigammaJet q m z) G := by
  have hhom : (qPolyJetEval q m z).comp (MvPolynomial.map Polynomial.C)
      = (eval₂Hom (Polynomial.evalRingHom z) (qDigammaJet q m z)
          : MvPolynomial (Fin m) (Polynomial ℂ) →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, MvPolynomial.map_C, qPolyJetEval_C, qCoeffEval_C, eval₂Hom_C,
        Polynomial.coe_evalRingHom]
    · intro i
      rw [RingHom.comp_apply, MvPolynomial.map_X, qPolyJetEval_X, eval₂Hom_X']
  exact RingHom.congr_fun hhom G

/-! ## Γ_q-power relations with cleared coefficients -/

/-- A cleared `Γ_q`-power relation: jet polynomials `Q 0, …, Q D` over `ℂ(z,u)` with a common
denominator and integral forms whose `Γ_q`-power combination vanishes on the half-plane. -/
def QGammaPowerRel (q : RealEulerNome) (m D : ℕ)
    (Q : ℕ → MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) : Prop :=
  ∃ d : Polynomial (Polynomial ℂ), d ≠ 0 ∧
    ∃ G : ℕ → MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)),
      (∀ k, k ≤ D → MvPolynomial.map toQField (G k) = C (toQField d) * Q k) ∧
      ∀ z ∈ qHalfPlane,
        ∑ k ∈ Finset.range (D + 1), qGammaOn q z ^ k * qPolyJetEval q m z (G k) = 0

private theorem qCleared_eq_zero {m : ℕ} {d : Polynomial (Polynomial ℂ)} (hd : d ≠ 0)
    {G : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))}
    {Q : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))}
    (hmap : MvPolynomial.map toQField G = C (toQField d) * Q)
    (hG : G = 0) : Q = 0 := by
  rw [hG, map_zero] at hmap
  have hC : (C (toQField d) : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) ≠ 0 := by
    intro h0
    exact toQField_ne_zero hd (MvPolynomial.C_injective _ _ (by rw [h0, map_zero]))
  rcases mul_eq_zero.mp hmap.symm with h | h
  · exact absurd h hC
  · exact h

private theorem qCleared_of_eq_zero {m : ℕ} {d : Polynomial (Polynomial ℂ)}
    {G : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))}
    {Q : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))}
    (hmap : MvPolynomial.map toQField G = C (toQField d) * Q)
    (hQ : Q = 0) : G = 0 := by
  rw [hQ, mul_zero] at hmap
  exact MvPolynomial.map_injective _ toQField_injective (by rw [hmap, map_zero])

/-! ## The elimination -/

/-- **The Γ_q-power elimination**: a cleared `Γ_q`-power relation has all coefficients zero. -/
theorem qGammaPowerRel_eq_zero (q : RealEulerNome) {m : ℕ} :
    ∀ (D : ℕ) (Q : ℕ → MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))),
      QGammaPowerRel q m D Q → ∀ k, k ≤ D → Q k = 0 := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro Q hrel k hk
    obtain ⟨d, hd, G, hmap, hval⟩ := hrel
    cases D with
    | zero =>
        interval_cases k
        refine qCleared_eq_zero hd (hmap 0 le_rfl) ?_
        apply annihilatesQDigamma_eq_zero q
        intro z hz
        have h1 := hval z hz
        simpa using h1
    | succ D =>
        by_cases hQtop : Q (D + 1) = 0
        · -- the top coefficient vanishes: restrict to degree `D`
          have hGtop : G (D + 1) = 0 := qCleared_of_eq_zero (hmap (D + 1) le_rfl) hQtop
          have hrestrict : QGammaPowerRel q m D Q := by
            refine ⟨d, hd, G, fun j hj => hmap j (by omega), fun z hz => ?_⟩
            have h1 := hval z hz
            rw [Finset.sum_range_succ, hGtop, map_zero, mul_zero, add_zero] at h1
            exact h1
          rcases Nat.lt_or_ge k (D + 1) with hk' | hk'
          · exact ih D (by omega) Q hrestrict k (by omega)
          · have hkeq : k = D + 1 := by omega
            rw [hkeq]
            exact hQtop
        · -- the top coefficient survives: eliminate and refute
          exfalso
          set N : ℕ := (Finset.range (D + 2)).sup (fun j => (G j).totalDegree) with hN_def
          have hNle : ∀ j, j ≤ D + 1 → (G j).totalDegree ≤ N := by
            intro j hj
            rw [hN_def]
            exact Finset.le_sup (f := fun j => (G j).totalDegree)
              (Finset.mem_range.mpr (by omega))
          set T : ℕ → MvPolynomial (Fin m) (RatFunc (RatFunc ℂ)) := fun j =>
            C (qMult q ^ j) * jetTranslateGen (qShift q) (qIncr q) m (Q j) * Q (D + 1)
              - C (qMult q ^ (D + 1)) * Q j
                * jetTranslateGen (qShift q) (qIncr q) m (Q (D + 1)) with hT_def
          set G' : ℕ → MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)) := fun j =>
            C (qMultInt q ^ j) * qClearedShift q m N (G j) * G (D + 1)
              - C (qMultInt q ^ (D + 1)) * G j * qClearedShift q m N (G (D + 1))
            with hG'_def
          set d' : Polynomial (Polynomial ℂ) :=
            qDen m ^ N * qIntShift q d * d with hd'_def
          have hd' : d' ≠ 0 :=
            mul_ne_zero (mul_ne_zero (pow_ne_zero _ (qDen_ne_zero m))
              (qIntShift_ne_zero q hd)) hd
          have hmapC : ∀ j, j ≤ D + 1 →
              MvPolynomial.map toQField (qClearedShift q m N (G j))
                = C (toQField (qDen m ^ N * qIntShift q d))
                  * jetTranslateGen (qShift q) (qIncr q) m (Q j) := by
            intro j hj
            rw [map_qClearedShift q m N (G j) (hNle j hj), hmap j hj,
              map_mul (jetTranslateGen (qShift q) (qIncr q) m), jetTranslate_CGen,
              ← toQField_qIntShift]
            simp only [map_mul]
            ring
          have hmap' : ∀ j, j ≤ D →
              MvPolynomial.map toQField (G' j) = C (toQField d') * T j := by
            intro j hj
            rw [hG'_def]
            simp only []
            rw [map_sub, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C,
              MvPolynomial.map_C, hmapC j (by omega), hmapC (D + 1) le_rfl,
              hmap j (by omega), hmap (D + 1) le_rfl, hT_def, hd'_def]
            simp only [map_pow, map_mul, toQField_qMultInt]
            ring
          have hval' : ∀ z ∈ qHalfPlane,
              ∑ j ∈ Finset.range (D + 1),
                qGammaOn q z ^ j * qPolyJetEval q m z (G' j) = 0 := by
            intro z hz
            have hz1 : z + 1 ∈ qHalfPlane := mem_qHalfPlane_add_one hz
            set Mz : ℂ := qCoeffEval q z (qMultInt q) with hMz_def
            set K : ℂ := ((1 - qPoint q z) ^ m) ^ N with hK_def
            set A : ℕ → ℂ := fun j => qPolyJetEval q m z (G j) with hA_def
            set B : ℕ → ℂ := fun j => qPolyJetEval q m (z + 1) (G j) with hB_def
            have hGterm : ∀ j ∈ Finset.range (D + 1), qGammaOn q z ^ j
                  * qPolyJetEval q m z (G' j)
                = qGammaOn q z ^ j
                  * (Mz ^ j * (K * B j) * A (D + 1)
                    - Mz ^ (D + 1) * A j * (K * B (D + 1))) := by
              intro j hj
              have hjD : j ≤ D + 1 := by
                have := Finset.mem_range.mp hj
                omega
              congr 1
              rw [hG'_def]
              simp only []
              rw [map_sub, map_mul, map_mul, map_mul, map_mul, qPolyJetEval_C,
                qPolyJetEval_C, map_pow, map_pow,
                qPolyJetEval_qClearedShift q (hNle j hjD) hz,
                qPolyJetEval_qClearedShift q (hNle (D + 1) le_rfl) hz]
            have hshift : qGammaOn q (z + 1) = Mz * qGammaOn q z := by
              rw [hMz_def, qCoeffEval_qMultInt, qGammaOn_shift q hz]
            have hsum1 : ∑ j ∈ Finset.range (D + 1), (Mz * qGammaOn q z) ^ j * B j
                = -((Mz * qGammaOn q z) ^ (D + 1) * B (D + 1)) := by
              have h2 := hval (z + 1) hz1
              rw [Finset.sum_range_succ] at h2
              rw [hshift] at h2
              exact eq_neg_of_add_eq_zero_left h2
            have hsum2 : ∑ j ∈ Finset.range (D + 1), qGammaOn q z ^ j * A j
                = -(qGammaOn q z ^ (D + 1) * A (D + 1)) := by
              have h1 := hval z hz
              rw [Finset.sum_range_succ] at h1
              exact eq_neg_of_add_eq_zero_left h1
            rw [Finset.sum_congr rfl hGterm]
            have hexpand : ∑ j ∈ Finset.range (D + 1), qGammaOn q z ^ j
                  * (Mz ^ j * (K * B j) * A (D + 1)
                    - Mz ^ (D + 1) * A j * (K * B (D + 1)))
                = K * A (D + 1)
                    * (∑ j ∈ Finset.range (D + 1), (Mz * qGammaOn q z) ^ j * B j)
                  - K * Mz ^ (D + 1) * B (D + 1)
                    * (∑ j ∈ Finset.range (D + 1), qGammaOn q z ^ j * A j) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow]
              ring
            rw [hexpand, hsum1, hsum2]
            ring
          have hTzero : ∀ j, j ≤ D → T j = 0 :=
            ih D (by omega) T ⟨d', hd', G', hmap', hval'⟩
          by_cases hlow : ∀ j, j ≤ D → Q j = 0
          · -- single-term relation: the top must vanish too
            apply hQtop
            refine qCleared_eq_zero hd (hmap (D + 1) le_rfl) ?_
            apply annihilatesQDigamma_eq_zero q
            intro z hz
            have h1 := hval z hz
            have hGlow : ∀ j, j ≤ D → G j = 0 := fun j hj =>
              qCleared_of_eq_zero (hmap j (by omega)) (hlow j hj)
            rw [Finset.sum_range_succ] at h1
            rw [Finset.sum_eq_zero (fun j hj => by
              rw [hGlow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), map_zero,
                mul_zero]), zero_add] at h1
            have hΓ : qGammaOn q z ^ (D + 1) ≠ 0 :=
              pow_ne_zero _ (qGammaOn_ne_zero q hz)
            exact (mul_eq_zero.mp h1).resolve_left hΓ
          · -- a surviving lower coefficient: the eigenrelation
            simp only [not_forall] at hlow
            obtain ⟨d₀, hd₀le, hd₀ne⟩ := hlow
            have hTd₀ := hTzero d₀ hd₀le
            rw [hT_def] at hTd₀
            simp only [] at hTd₀
            have hCd₀ : (C (qMult q ^ d₀) : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) ≠ 0 := by
              intro h0
              exact pow_ne_zero d₀ (qMult_ne_zero q)
                (MvPolynomial.C_injective _ _ (by rw [h0, map_zero]))
            have heig : jetTranslateGen (qShift q) (qIncr q) m (Q d₀) * Q (D + 1)
                = C (qMult q ^ (D + 1 - d₀))
                  * (Q d₀ * jetTranslateGen (qShift q) (qIncr q) m (Q (D + 1))) := by
              apply mul_left_cancel₀ hCd₀
              have h0 := sub_eq_zero.mp hTd₀
              have hsplit : (qMult q) ^ (D + 1)
                  = qMult q ^ d₀ * qMult q ^ (D + 1 - d₀) := by
                rw [← pow_add]
                congr 1
                omega
              rw [hsplit, map_mul] at h0
              linear_combination h0
            exact no_shift_eigenrelationGen (qShift q) (qShiftInv q) (qIncr q)
              (qShiftInv_qShift q) (qShift_qShiftInv q)
              (pow_ne_zero _ (qMult_ne_zero q))
              (fun {r} hr => qShift_eq_qMult_pow_mul_eq_zero q (by omega) hr)
              hd₀ne hQtop heig

/-! ## Pastro's theorem -/

/-- **The q-Gamma function is hypertranscendental** (Pastro's q-analogue of Hölder's theorem):
Jackson's `Γ_q` satisfies no algebraic differential equation over `ℂ[z]` on the half-plane
`Re z > 0`. -/
theorem qGamma_jet_annihilator_eq_zero (q : RealEulerNome) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ z ∈ qHalfPlane, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (qGammaOn q) z) P = 0) :
    P = 0 := by
  classical
  set H := reshapeJet n P with hH_def
  set Q : ℕ → MvPolynomial (Fin (n + 1)) (RatFunc (RatFunc ℂ)) := fun dd =>
    MvPolynomial.map toQField (MvPolynomial.map Polynomial.C (bellGraded n H dd))
    with hQ_def
  have hmap1 : ∀ k, k ≤ H.totalDegree →
      MvPolynomial.map toQField (MvPolynomial.map Polynomial.C (bellGraded n H k))
        = C (toQField 1) * Q k := by
    intro k _
    rw [hQ_def, map_one, MvPolynomial.C_1, one_mul]
  have hrel : QGammaPowerRel q (n + 1) H.totalDegree Q := by
    refine ⟨1, one_ne_zero,
      fun dd => MvPolynomial.map Polynomial.C (bellGraded n H dd), hmap1, ?_⟩
    intro z hz
    have hcons : (fun j : Fin (n + 1) => qGammaOn q z
        * eval (qDigammaJet q (n + 1) z) (bellAt n (j : ℕ) (le_of_lt j.isLt)))
        = fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (qGammaOn q) z := by
      funext j
      rw [← qGamma_iteratedDeriv_eq_bellAt q (j : ℕ) (le_of_lt j.isLt) hz]
    have hexp := eval₂_bell_expansion n H z (qGammaOn q z) (qDigammaJet q (n + 1) z)
    rw [hcons] at hexp
    have hLHS : eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (qGammaOn q) z) H = 0 := by
      rw [hH_def, eval₂_reshapeJet]
      exact hPz z hz
    rw [hLHS] at hexp
    rw [show (∑ k ∈ Finset.range (H.totalDegree + 1), qGammaOn q z ^ k
        * qPolyJetEval q (n + 1) z (MvPolynomial.map Polynomial.C (bellGraded n H k)))
        = ∑ k ∈ Finset.range (H.totalDegree + 1), qGammaOn q z ^ k
          * eval₂ (Polynomial.evalRingHom z) (qDigammaJet q (n + 1) z)
              (bellGraded n H k) from
      Finset.sum_congr rfl fun k _ => by rw [qPolyJetEval_map_C]]
    exact hexp.symm
  have hall := qGammaPowerRel_eq_zero q H.totalDegree Q hrel
  have hGzero : ∀ dd, dd ≤ H.totalDegree → bellGraded n H dd = 0 := by
    intro dd hdd
    have h0 := qCleared_of_eq_zero (hmap1 dd hdd) (hall dd hdd)
    exact MvPolynomial.map_injective _ Polynomial.C_injective (by rw [h0, map_zero])
  -- pointwise vanishing off the Γ_q-slot hyperplane, by Bell surjectivity
  have hvanish : ∀ u : Fin (n + 2) → ℂ, u 1 ≠ 0 → eval u P = 0 := by
    intro u hu1
    obtain ⟨w, hw⟩ := exists_bellAt_solution n (fun k =>
      if h : (k : ℕ) + 2 < n + 2 then u ⟨(k : ℕ) + 2, h⟩ / u 1 else 0)
    have hvec : (Fin.cons (u 0) (fun j : Fin (n + 1) => u 1
        * eval w (bellAt n (j : ℕ) (le_of_lt j.isLt))) : Fin (n + 2) → ℂ) = u := by
      funext i
      induction i using Fin.cases with
      | zero => rw [Fin.cons_zero]
      | succ j =>
          rw [Fin.cons_succ]
          induction j using Fin.cases with
          | zero =>
              rw [show bellAt n ((0 : Fin (n + 1)) : ℕ)
                  (le_of_lt (0 : Fin (n + 1)).isLt) = 1 from bellAt_zero n _]
              rw [map_one, mul_one]
              rfl
          | succ i =>
              have hidx : ((i.succ : Fin (n + 1)) : ℕ)
                  = ((i.castSucc : Fin (n + 1)) : ℕ) + 1 := by
                simp
              rw [show bellAt n ((i.succ : Fin (n + 1)) : ℕ)
                    (le_of_lt (i.succ : Fin (n + 1)).isLt)
                  = bellAt n (((i.castSucc : Fin (n + 1)) : ℕ) + 1) (i.castSucc).isLt
                  from bellAt_congr hidx _ _]
              rw [hw i.castSucc]
              have hlt : ((i.castSucc : Fin (n + 1)) : ℕ) + 2 < n + 2 := by
                have := i.isLt
                simp only [Fin.val_castSucc]
                omega
              rw [dif_pos hlt, mul_div_cancel₀ _ hu1]
              congr 1
    have hval0 : eval u P
        = ∑ dd ∈ Finset.range (H.totalDegree + 1),
            (u 1) ^ dd * eval₂ (Polynomial.evalRingHom (u 0)) w (bellGraded n H dd) := by
      conv_lhs => rw [← hvec]
      rw [← eval₂_reshapeJet n (u 0)
        (fun j : Fin (n + 1) => u 1 * eval w (bellAt n (j : ℕ) (le_of_lt j.isLt))) P]
      exact eval₂_bell_expansion n H (u 0) (u 1) w
    rw [hval0]
    refine Finset.sum_eq_zero fun dd hdd => ?_
    rw [hGzero dd (Nat.lt_succ_iff.mp (Finset.mem_range.mp hdd)), eval₂_zero, mul_zero]
  have hXP : (MvPolynomial.X 1 : MvPolynomial (Fin (n + 2)) ℂ) * P = 0 := by
    apply MvPolynomial.funext
    intro u
    rw [map_mul, eval_X, map_zero]
    by_cases hu : u 1 = 0
    · rw [hu, zero_mul]
    · rw [hvanish u hu, mul_zero]
  exact (mul_eq_zero.mp hXP).resolve_left (MvPolynomial.X_ne_zero 1)

end

end GaloisForLFunctions.HTGeometry
