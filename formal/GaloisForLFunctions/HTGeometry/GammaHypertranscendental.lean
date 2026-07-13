import GaloisForLFunctions.HTGeometry.GammaShiftEigenrelation
import GaloisForLFunctions.HTGeometry.GammaBellSubstitution

/-!
# Hölder's theorem: the Gamma function is hypertranscendental

`Γ` satisfies no algebraic differential equation over `ℂ[s]`:
`Hypertranscendental Complex.Gamma` — Hölder's 1887 theorem, the founding statement of the
branch, machine-checked.

The proof transfers Hölder's theorem for the digamma function through the Bell
substitution.  A differential polynomial for `Γ` becomes, after `Γ⁽ᵏ⁾ = Γ·B_k(ψ-jets)`, a
`Γ`-power relation `Σ_d Γ^d·Q_d(s, ψ-jets) = 0` whose coefficients are digamma jet
polynomials (`bellGraded`); the triangular pointwise surjectivity of the Bell value map
shows the coefficients cannot all vanish unless the original polynomial was zero.  The
relation is eliminated by induction on the `Γ`-degree against the shift `s ↦ s+1`: the
functional equation `Γ(s+1) = s·Γ(s)` contributes the factor `s^k` in degree `k`, the
digamma jets transform by the jet substitution, and cross-multiplying kills the top
degree.  The eliminated relation either terminates in a single term — killed by the
polynomial-level Hölder theorem (`polyJetEval_offPole_eq_zero`) — or in a difference
eigenrelation `σ(f)·g = Xᵉ·f·σ(g)`, refuted by the degree obstruction
(`no_shift_eigenrelation`).
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-! ## Γ-power relations with cleared coefficients -/

/-- A cleared `Γ`-power relation: rational-coefficient digamma jet polynomials
`Q 0, …, Q D` with a common denominator and polynomial forms whose `Γ`-power combination
vanishes off the poles. -/
def GammaPowerRel (m D : ℕ) (Q : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)) : Prop :=
  ∃ d : Polynomial ℂ, d ≠ 0 ∧ ∃ G : ℕ → MvPolynomial (Fin m) (Polynomial ℂ),
    (∀ k, k ≤ D → MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (G k)
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * Q k) ∧
    ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) →
      ∑ k ∈ Finset.range (D + 1), Complex.Gamma z ^ k * polyJetEval m z (G k) = 0

private theorem cleared_eq_zero {m : ℕ} {d : Polynomial ℂ} (hd : d ≠ 0)
    {G : MvPolynomial (Fin m) (Polynomial ℂ)} {Q : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * Q)
    (hG : G = 0) : Q = 0 := by
  rw [hG, map_zero] at hmap
  have hC : (MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d)
      : MvPolynomial (Fin m) (RatFunc ℂ)) ≠ 0 := by
    intro h0
    exact algebraMap_ratFunc_ne_zero hd
      (MvPolynomial.C_injective _ _ (by rw [h0, map_zero]))
  rcases mul_eq_zero.mp hmap.symm with h | h
  · exact absurd h hC
  · exact h

private theorem cleared_of_eq_zero {m : ℕ} {d : Polynomial ℂ}
    {G : MvPolynomial (Fin m) (Polynomial ℂ)} {Q : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * Q)
    (hQ : Q = 0) : G = 0 := by
  rw [hQ, mul_zero] at hmap
  exact MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    (by rw [hmap, map_zero])

/-! ## The elimination -/

/-- **The Γ-power elimination**: a cleared `Γ`-power relation has all coefficients zero.
Induction on the `Γ`-degree: the shifted relation carries the factor `s^k` in degree `k`
by the `Γ` functional equation; cross-multiplying against the top coefficient eliminates
it, the inductive hypothesis kills the eliminated relation, and the surviving identities
are difference eigenrelations — refuted by the degree obstruction — unless all lower
coefficients vanish, in which case the single surviving term is killed by the
polynomial-level Hölder theorem. -/
theorem gammaPowerRel_eq_zero {m : ℕ} :
    ∀ (D : ℕ) (Q : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)),
      GammaPowerRel m D Q → ∀ k, k ≤ D → Q k = 0 := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro Q hrel k hk
    obtain ⟨d, hd, G, hmap, hval⟩ := hrel
    cases D with
    | zero =>
        interval_cases k
        refine cleared_eq_zero hd (hmap 0 le_rfl) ?_
        apply polyJetEval_offPole_eq_zero
        intro z hz
        have h1 := hval z hz
        simpa using h1
    | succ D =>
        by_cases hQtop : Q (D + 1) = 0
        · -- the top coefficient vanishes: restrict to degree `D`
          have hGtop : G (D + 1) = 0 := cleared_of_eq_zero (hmap (D + 1) le_rfl) hQtop
          have hrestrict : GammaPowerRel m D Q := by
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
          set N : ℕ := (Finset.range (D + 2)).sup (fun j => (G j).totalDegree)
            with hN_def
          have hNle : ∀ j, j ≤ D + 1 → (G j).totalDegree ≤ N := by
            intro j hj
            rw [hN_def]
            exact Finset.le_sup (f := fun j => (G j).totalDegree)
              (Finset.mem_range.mpr (by omega))
          set T : ℕ → MvPolynomial (Fin m) (RatFunc ℂ) := fun j =>
            MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ j)
                * jetTranslate m (Q j) * Q (D + 1)
              - MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ (D + 1))
                * Q j * jetTranslate m (Q (D + 1)) with hT_def
          set G' : ℕ → MvPolynomial (Fin m) (Polynomial ℂ) := fun j =>
            MvPolynomial.C ((Polynomial.X : Polynomial ℂ) ^ j)
                * clearedShift m N (G j) * G (D + 1)
              - MvPolynomial.C ((Polynomial.X : Polynomial ℂ) ^ (D + 1))
                * G j * clearedShift m N (G (D + 1)) with hG'_def
          set d' : Polynomial ℂ :=
            Polynomial.X ^ (m * N) * d.comp (Polynomial.X + Polynomial.C 1) * d
            with hd'_def
          have hd' : d' ≠ 0 :=
            mul_ne_zero (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
              (comp_X_add_C_one_ne_zero hd)) hd
          have hmapC : ∀ j, j ≤ D + 1 →
              MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
                  (clearedShift m N (G j))
                = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ)
                    (Polynomial.X ^ (m * N)
                      * d.comp (Polynomial.X + Polynomial.C 1)))
                  * jetTranslate m (Q j) := by
            intro j hj
            rw [map_clearedShift m N (G j) (hNle j hj), hmap j hj,
              map_mul (jetTranslate m), jetTranslate_C, ratShift_algebraMap]
            simp only [map_mul]
            ring
          have hmap' : ∀ j, j ≤ D →
              MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (G' j)
                = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d') * T j := by
            intro j hj
            rw [hG'_def]
            simp only []
            rw [map_sub, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C,
              MvPolynomial.map_C, hmapC j (by omega), hmapC (D + 1) le_rfl,
              hmap j (by omega), hmap (D + 1) le_rfl, hT_def, hd'_def]
            simp only [map_pow, map_mul, RatFunc.algebraMap_X]
            ring
          have hval' : ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) →
              ∑ j ∈ Finset.range (D + 1),
                Complex.Gamma z ^ j * polyJetEval m z (G' j) = 0 := by
            intro z hz
            have hz0 : z ≠ 0 := by simpa using hz 0
            have hz1 : ∀ p : ℕ, z + 1 ≠ -(p : ℂ) := by
              intro p hEq
              exact hz (p + 1) (by push_cast; linear_combination hEq)
            set A : ℕ → ℂ := fun j => polyJetEval m z (G j) with hA_def
            set B : ℕ → ℂ := fun j => polyJetEval m (z + 1) (G j) with hB_def
            have hGterm : ∀ j ∈ Finset.range (D + 1), Complex.Gamma z ^ j
                  * polyJetEval m z (G' j)
                = Complex.Gamma z ^ j
                  * (z ^ j * (z ^ (m * N) * B j) * A (D + 1)
                    - z ^ (D + 1) * A j * (z ^ (m * N) * B (D + 1))) := by
              intro j hj
              have hjD : j ≤ D + 1 := by
                have := Finset.mem_range.mp hj
                omega
              congr 1
              rw [hG'_def]
              simp only []
              rw [map_sub, map_mul, map_mul, map_mul, map_mul, polyJetEval_C,
                polyJetEval_C, Polynomial.eval_pow, Polynomial.eval_X,
                Polynomial.eval_pow, Polynomial.eval_X,
                polyJetEval_clearedShift (hNle j hjD) hz,
                polyJetEval_clearedShift (hNle (D + 1) le_rfl) hz]
            have hsum1 : ∑ j ∈ Finset.range (D + 1),
                  (z * Complex.Gamma z) ^ j * B j
                = -((z * Complex.Gamma z) ^ (D + 1) * B (D + 1)) := by
              have h2 := hval (z + 1) hz1
              rw [Finset.sum_range_succ] at h2
              rw [Complex.Gamma_add_one z hz0] at h2
              exact eq_neg_of_add_eq_zero_left h2
            have hsum2 : ∑ j ∈ Finset.range (D + 1), Complex.Gamma z ^ j * A j
                = -(Complex.Gamma z ^ (D + 1) * A (D + 1)) := by
              have h1 := hval z hz
              rw [Finset.sum_range_succ] at h1
              exact eq_neg_of_add_eq_zero_left h1
            rw [Finset.sum_congr rfl hGterm]
            have hexpand : ∑ j ∈ Finset.range (D + 1), Complex.Gamma z ^ j
                  * (z ^ j * (z ^ (m * N) * B j) * A (D + 1)
                    - z ^ (D + 1) * A j * (z ^ (m * N) * B (D + 1)))
                = z ^ (m * N) * A (D + 1)
                    * (∑ j ∈ Finset.range (D + 1),
                        (z * Complex.Gamma z) ^ j * B j)
                  - z ^ (m * N) * z ^ (D + 1) * B (D + 1)
                    * (∑ j ∈ Finset.range (D + 1),
                        Complex.Gamma z ^ j * A j) := by
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
            refine cleared_eq_zero hd (hmap (D + 1) le_rfl) ?_
            apply polyJetEval_offPole_eq_zero
            intro z hz
            have h1 := hval z hz
            have hGlow : ∀ j, j ≤ D → G j = 0 := fun j hj =>
              cleared_of_eq_zero (hmap j (by omega)) (hlow j hj)
            rw [Finset.sum_range_succ] at h1
            rw [Finset.sum_eq_zero (fun j hj => by
              rw [hGlow j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), map_zero,
                mul_zero]), zero_add] at h1
            have hΓ : Complex.Gamma z ^ (D + 1) ≠ 0 :=
              pow_ne_zero _ (Complex.Gamma_ne_zero hz)
            exact (mul_eq_zero.mp h1).resolve_left hΓ
          · -- a surviving lower coefficient: the eigenrelation
            simp only [not_forall] at hlow
            obtain ⟨d₀, hd₀le, hd₀ne⟩ := hlow
            have hTd₀ := hTzero d₀ hd₀le
            rw [hT_def] at hTd₀
            simp only [] at hTd₀
            have hCd₀ : (MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ d₀)
                : MvPolynomial (Fin m) (RatFunc ℂ)) ≠ 0 := by
              intro h0
              exact pow_ne_zero d₀ ratFuncX_ne_zero
                (MvPolynomial.C_injective _ _ (by rw [h0, map_zero]))
            have heig : jetTranslate m (Q d₀) * Q (D + 1)
                = MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ (D + 1 - d₀))
                  * (Q d₀ * jetTranslate m (Q (D + 1))) := by
              apply mul_left_cancel₀ hCd₀
              have h0 := sub_eq_zero.mp hTd₀
              have hsplit : ((RatFunc.X : RatFunc ℂ)) ^ (D + 1)
                  = RatFunc.X ^ d₀ * RatFunc.X ^ (D + 1 - d₀) := by
                rw [← pow_add]
                congr 1
                omega
              rw [hsplit, map_mul] at h0
              linear_combination h0
            exact no_shift_eigenrelation hd₀ne hQtop
              (by omega : 1 ≤ D + 1 - d₀) heig

/-! ## Expanding a Γ-jet polynomial along the Bell substitution -/

theorem polyJetEval_eq_eval₂ (m : ℕ) (z : ℂ)
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) :
    polyJetEval m z G
      = eval₂ (Polynomial.evalRingHom z) (digammaJet m z) G := rfl

/-- Generic reshaped evaluation: any jet vector in the value slots, the point evaluated in
the coefficients. -/
theorem eval₂_reshapeJet (n : ℕ) (z : ℂ) (v : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    eval₂ (Polynomial.evalRingHom z) v (reshapeJet n P) = eval (Fin.cons z v) P := by
  have hhom : ((eval₂Hom (Polynomial.evalRingHom z) v).comp (reshapeJet n))
      = (MvPolynomial.eval (Fin.cons z v) : _ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [reshapeJet]
    · intro i
      induction i using Fin.cases with
      | zero => simp [reshapeJet]
      | succ j => simp [reshapeJet, Fin.cons_succ]
  exact RingHom.congr_fun hhom P

theorem bellAt_congr {n : ℕ} {k₁ k₂ : ℕ} (h : k₁ = k₂) (h₁ : k₁ ≤ n + 1)
    (h₂ : k₂ ≤ n + 1) : bellAt n k₁ h₁ = bellAt n k₂ h₂ := by
  subst h
  rfl

theorem bellAt_zero (n : ℕ) (h : 0 ≤ n + 1) : bellAt n 0 h = 1 := by
  rw [bellAt, bellCore_zero]
  exact map_one _

/-- The Bell monomial of a jet exponent. -/
def bellProd (n : ℕ) (α : Fin (n + 1) →₀ ℕ) : MvPolynomial (Fin (n + 1)) ℂ :=
  ∏ j : Fin (n + 1), (bellAt n (j : ℕ) (le_of_lt j.isLt)) ^ (α j)

/-- The `Γ`-degree-graded Bell coefficients of a reshaped differential polynomial. -/
def bellGraded (n : ℕ) (H : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) (dd : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  ∑ α ∈ H.support.filter (fun α => degSum α = dd),
    MvPolynomial.C (MvPolynomial.coeff α H)
      * MvPolynomial.map (Polynomial.C) (bellProd n α)

theorem eval₂_map_polyC {n : ℕ} (z : ℂ) (w : Fin (n + 1) → ℂ)
    (B : MvPolynomial (Fin (n + 1)) ℂ) :
    eval₂ (Polynomial.evalRingHom z) w (MvPolynomial.map (Polynomial.C) B)
      = eval w B := by
  rw [eval₂_map]
  have hcomp : (Polynomial.evalRingHom z).comp (Polynomial.C : ℂ →+* Polynomial ℂ)
      = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    simp
  rw [hcomp]
  rfl

/-- **The Bell expansion**: evaluating a reshaped differential polynomial on jet values of
the form `γ·(Bell values)` produces the `γ`-power expansion with the graded Bell
coefficients. -/
theorem eval₂_bell_expansion (n : ℕ) (H : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
    (z γ : ℂ) (w : Fin (n + 1) → ℂ) :
    eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (n + 1) => γ * eval w (bellAt n (j : ℕ) (le_of_lt j.isLt))) H
      = ∑ dd ∈ Finset.range (H.totalDegree + 1),
          γ ^ dd * eval₂ (Polynomial.evalRingHom z) w (bellGraded n H dd) := by
  rw [eval₂_eq']
  have hmaps : ∀ α ∈ H.support, degSum α ∈ Finset.range (H.totalDegree + 1) :=
    fun α hα => Finset.mem_range.mpr (Nat.lt_succ_of_le (MvPolynomial.le_totalDegree hα))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun α => (Polynomial.evalRingHom z) (MvPolynomial.coeff α H)
      * ∏ i : Fin (n + 1),
          (γ * eval w (bellAt n (i : ℕ) (le_of_lt i.isLt))) ^ (α i))]
  refine Finset.sum_congr rfl fun dd _ => ?_
  rw [bellGraded, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  obtain ⟨hαsupp, hαdeg⟩ := Finset.mem_filter.mp hα
  rw [eval₂_mul, eval₂_map_polyC, eval₂_C]
  have hprod : ∏ i : Fin (n + 1),
      (γ * eval w (bellAt n (i : ℕ) (le_of_lt i.isLt))) ^ (α i)
      = γ ^ dd * eval w (bellProd n α) := by
    rw [bellProd, ← hαdeg]
    rw [Finset.prod_congr rfl (fun i _ => mul_pow γ _ (α i)), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, ← degSum_eq_univ_sum]
    congr 1
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
  rw [hprod]
  ring

/-! ## Hölder's theorem -/

/-- **The Gamma function is hypertranscendental** (Hölder, 1887): `Γ` satisfies no
algebraic differential equation over `ℂ[s]`.  Machine-checked by transferring the digamma
form through the Bell substitution and eliminating the resulting `Γ`-power relation
against the functional equation `Γ(s+1) = s·Γ(s)`. -/
theorem hypertranscendental_gamma : Hypertranscendental Complex.Gamma := by
  rintro ⟨n, P, hP0, hPz⟩
  set H := reshapeJet n P with hH_def
  have hH0 : H ≠ 0 := fun h0 =>
    hP0 (reshapeJet_injective n (by rw [← hH_def, h0, map_zero]))
  set Q : ℕ → MvPolynomial (Fin (n + 1)) (RatFunc ℂ) := fun dd =>
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (bellGraded n H dd)
    with hQ_def
  have hmap1 : ∀ k, k ≤ H.totalDegree →
      MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (bellGraded n H k)
        = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) 1) * Q k := by
    intro k _
    rw [hQ_def, map_one, MvPolynomial.C_1, one_mul]
  have hrel : GammaPowerRel (n + 1) H.totalDegree Q := by
    refine ⟨1, one_ne_zero, fun dd => bellGraded n H dd, hmap1, ?_⟩
    intro z hz
    have hcons : (fun j : Fin (n + 1) => Complex.Gamma z
        * eval (digammaJet (n + 1) z) (bellAt n (j : ℕ) (le_of_lt j.isLt)))
        = fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.Gamma z := by
      funext j
      rw [← gamma_iteratedDeriv_eq_bellAt (j : ℕ) (le_of_lt j.isLt) hz]
    have hexp := eval₂_bell_expansion n H z (Complex.Gamma z) (digammaJet (n + 1) z)
    rw [hcons] at hexp
    have hLHS : eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.Gamma z) H = 0 := by
      rw [hH_def, eval₂_reshapeJet]
      exact hPz z
    rw [hLHS] at hexp
    rw [show (∑ k ∈ Finset.range (H.totalDegree + 1), Complex.Gamma z ^ k
        * polyJetEval (n + 1) z (bellGraded n H k))
        = ∑ k ∈ Finset.range (H.totalDegree + 1), Complex.Gamma z ^ k
          * eval₂ (Polynomial.evalRingHom z) (digammaJet (n + 1) z)
              (bellGraded n H k) from
      Finset.sum_congr rfl fun k _ => by rw [polyJetEval_eq_eval₂]]
    exact hexp.symm
  have hall := gammaPowerRel_eq_zero H.totalDegree Q hrel
  have hGzero : ∀ dd, dd ≤ H.totalDegree → bellGraded n H dd = 0 := fun dd hdd =>
    cleared_of_eq_zero (hmap1 dd hdd) (hall dd hdd)
  -- pointwise vanishing off the Γ-slot hyperplane, by Bell surjectivity
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
            (u 1) ^ dd * eval₂ (Polynomial.evalRingHom (u 0)) w (bellGraded n H dd)
        := by
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
  exact hP0 ((mul_eq_zero.mp hXP).resolve_left (MvPolynomial.X_ne_zero 1))

end GaloisForLFunctions

end
