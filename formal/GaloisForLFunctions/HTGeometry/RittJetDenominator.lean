import GaloisForLFunctions.HTGeometry.RittLogTowerQuasiInvariantResidual

/-!
# Denominators in the jet field of the affine logarithmic tower

Let `u` solve the affine transport equation of a Ritt frame and let its first `n` jets be
algebraically independent, so that the jet field `K(u, …, d^{n−1}u)` is the fraction field of the
polynomial ring in the jets.  An element `y` of that field has a reduced representation
`y = A(u)/B(u)` with `A` and `B` relatively prime; the reduced denominator `B` divides every
polynomial `P` with `P(u)·y` a polynomial in the jets.

If `y` moves affinely under the shift, `σ y = μ·y + t` with `t` a polynomial in the jets, the set of
such `P` is shift-stable, so `B` divides its own tower shift.  The tower shift preserves the weight
filtration and multiplication in a domain adds top weights, so the quotient has weight zero:
`towerShift B = μ'·B`.  The reduced denominator is therefore a shift eigenvector, and reading its
top weight coefficient against an eigen-coordinate `v` (`σ v = ρ⁻¹v`) gives

`B(u) = k·v^W`.

In particular `y·v^W` is a polynomial in the jets, and `y` itself is one as soon as no positive
power
of `v` lies in the jet field.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-! ### Top weights in a domain -/

theorem exists_top_weight {P : MvPolynomial (Fin n) K} (hP : P ≠ 0) :
    ∃ (W : ℕ) (d : Fin n →₀ ℕ), WLe n P W ∧ d ∈ P.support ∧
      Finsupp.weight (jetWeight n) d = W := by
  classical
  obtain ⟨d, hd, hmax⟩ := P.support.exists_max_image (Finsupp.weight (jetWeight n))
    (MvPolynomial.support_nonempty.mpr hP)
  exact ⟨_, d, fun e he => hmax e he, hd, rfl⟩

/-- **Top weights add.**  If the product `B·Q` has weight at most the top weight of `B`, then `Q`
has weight zero. -/
theorem wLe_zero_of_wLe_mul {B Q : MvPolynomial (Fin n) K} {W : ℕ} (hB : WLe n B W)
    {d : Fin n →₀ ℕ} (hd : d ∈ B.support) (hdW : Finsupp.weight (jetWeight n) d = W)
    (hBQ : WLe n (B * Q) W) : WLe n Q 0 := by
  classical
  by_cases hQ : Q = 0
  · rw [hQ]; exact wLe_zero 0
  obtain ⟨W', d', hQW, hd', hd'W⟩ := exists_top_weight hQ
  set Bt := weightedHomogeneousComponent (jetWeight n) W B with hBt
  set Qt := weightedHomogeneousComponent (jetWeight n) W' Q with hQt
  have hBt0 : Bt ≠ 0 := by
    intro h
    have := congrArg (coeff d) h
    rw [hBt, coeff_weightedHomogeneousComponent, if_pos hdW, coeff_zero] at this
    exact (MvPolynomial.mem_support_iff.mp hd) this
  have hQt0 : Qt ≠ 0 := by
    intro h
    have := congrArg (coeff d') h
    rw [hQt, coeff_weightedHomogeneousComponent, if_pos hd'W, coeff_zero] at this
    exact (MvPolynomial.mem_support_iff.mp hd') this
  have hhom : IsWeightedHomogeneous (jetWeight n) (Bt * Qt) (W + W') :=
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr (mul_ne_zero hBt0 hQt0)
  have heW : Finsupp.weight (jetWeight n) e = W + W' := hhom (MvPolynomial.mem_support_iff.mp he)
  -- the remainder has smaller weight
  have hB' : WLe n (B - Bt) (W - 1) := wLe_sub_weightedHomogeneousComponent hB
  have hQ' : WLe n (Q - Qt) (W' - 1) := wLe_sub_weightedHomogeneousComponent hQW
  have hrest : coeff e (B * Q - Bt * Qt) = 0 := by
    have hsplit : B * Q - Bt * Qt = (B - Bt) * (Q - Qt) + (B - Bt) * Qt + Bt * (Q - Qt) := by ring
    rw [hsplit, coeff_add, coeff_add]
    have h1 : coeff e ((B - Bt) * (Q - Qt)) = 0 := by
      by_contra hne
      have := (hB'.mul hQ') e (MvPolynomial.mem_support_iff.mpr hne)
      by_cases hW : W = 0
      · subst hW
        have hBz : B - Bt = 0 := by
          ext f
          rw [coeff_zero]
          by_contra hf
          have := hB' f (MvPolynomial.mem_support_iff.mpr hf)
          have hle := hB f (by
            rw [MvPolynomial.mem_support_iff]
            intro h0
            rw [coeff_sub, h0, zero_sub, neg_eq_zero, hBt, coeff_weightedHomogeneousComponent]
              at hf
            split_ifs at hf with hh
            · exact hf h0
            · exact hf rfl)
          rw [coeff_sub, hBt, coeff_weightedHomogeneousComponent,
            if_pos (by omega), sub_self] at hf
          exact hf rfl
        rw [hBz, zero_mul, coeff_zero] at hne
        exact hne rfl
      · by_cases hW' : W' = 0
        · subst hW'
          have hQz : Q - Qt = 0 := by
            ext f
            rw [coeff_zero]
            by_contra hf
            have hle := hQW f (by
              rw [MvPolynomial.mem_support_iff]
              intro h0
              rw [coeff_sub, h0, zero_sub, neg_eq_zero, hQt, coeff_weightedHomogeneousComponent]
                at hf
              split_ifs at hf with hh
              · exact hf h0
              · exact hf rfl)
            rw [coeff_sub, hQt, coeff_weightedHomogeneousComponent,
              if_pos (by omega), sub_self] at hf
            exact hf rfl
          rw [hQz, mul_zero, coeff_zero] at hne
          exact hne rfl
        · omega
    have h2 : coeff e ((B - Bt) * Qt) = 0 := by
      by_contra hne
      have := (hB'.mul (wLe_weightedHomogeneousComponent W' Q)) e
        (MvPolynomial.mem_support_iff.mpr hne)
      by_cases hW : W = 0
      · subst hW
        have hBz : B - Bt = 0 := by
          ext f
          rw [coeff_zero]
          by_contra hf
          have hle := hB f (by
            rw [MvPolynomial.mem_support_iff]
            intro h0
            rw [coeff_sub, h0, zero_sub, neg_eq_zero, hBt, coeff_weightedHomogeneousComponent]
              at hf
            split_ifs at hf with hh
            · exact hf h0
            · exact hf rfl)
          rw [coeff_sub, hBt, coeff_weightedHomogeneousComponent,
            if_pos (by omega), sub_self] at hf
          exact hf rfl
        rw [hBz, zero_mul, coeff_zero] at hne
        exact hne rfl
      · omega
    have h3 : coeff e (Bt * (Q - Qt)) = 0 := by
      by_contra hne
      have := ((wLe_weightedHomogeneousComponent W B).mul hQ') e
        (MvPolynomial.mem_support_iff.mpr hne)
      by_cases hW' : W' = 0
      · subst hW'
        have hQz : Q - Qt = 0 := by
          ext f
          rw [coeff_zero]
          by_contra hf
          have hle := hQW f (by
            rw [MvPolynomial.mem_support_iff]
            intro h0
            rw [coeff_sub, h0, zero_sub, neg_eq_zero, hQt, coeff_weightedHomogeneousComponent]
              at hf
            split_ifs at hf with hh
            · exact hf h0
            · exact hf rfl)
          rw [coeff_sub, hQt, coeff_weightedHomogeneousComponent,
            if_pos (by omega), sub_self] at hf
          exact hf rfl
        rw [hQz, mul_zero, coeff_zero] at hne
        exact hne rfl
      · omega
    rw [h1, h2, h3, add_zero, add_zero]
  have hcoef : coeff e (B * Q) ≠ 0 := by
    rw [coeff_sub, sub_eq_zero] at hrest
    rw [hrest]
    exact MvPolynomial.mem_support_iff.mp he
  have hle := hBQ e (MvPolynomial.mem_support_iff.mpr hcoef)
  have hW'0 : W' = 0 := by omega
  rw [hW'0] at hQW
  exact hQW

theorem eq_C_of_wLe_zero' {Q : MvPolynomial (Fin n) K} (hQ : WLe n Q 0) :
    Q = C (coeff 0 Q) := by
  have h := eq_zero_of_wLe_zero (F := Q - C (coeff 0 Q))
    (by
      intro e he
      rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_C] at he
      by_cases he0 : e = 0
      · subst he0; simp
      · rw [if_neg (Ne.symm he0), sub_zero] at he
        exact hQ e (MvPolynomial.mem_support_iff.mpr he))
    (by rw [coeff_sub, coeff_C, if_pos rfl, sub_self])
  exact sub_eq_zero.mp h

/-! ### Reduced fractions of jet-field elements -/

theorem exists_reduced_polynomial_fraction [DecidableEq K] (A B : MvPolynomial (Fin n) K)
    (hB : B ≠ 0) :
    ∃ A' B' : MvPolynomial (Fin n) K, B' ≠ 0 ∧ IsRelPrime A' B' ∧ A' * B = A * B' := by
  induction h : B.totalDegree using Nat.strong_induction_on generalizing A B with
  | _ m ih =>
      by_cases hrel : IsRelPrime A B
      · exact ⟨A, B, hB, hrel, rfl⟩
      · simp only [IsRelPrime, not_forall] at hrel
        obtain ⟨c, ⟨A₁, hA₁⟩, ⟨B₁, hB₁⟩, hc⟩ := hrel
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_mul] at hB₁
          exact hB hB₁
        have hB₁0 : B₁ ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hB₁
          exact hB hB₁
        have hcdeg : c.totalDegree ≠ 0 := by
          intro h0
          rw [totalDegree_eq_zero_iff_eq_C] at h0
          apply hc
          rw [h0]
          refine isUnit_iff_eq_C_of_isReduced.mpr ⟨coeff 0 c, ?_, rfl⟩
          refine isUnit_iff_ne_zero.mpr fun hz => hc0 ?_
          rw [h0, hz, map_zero]
        have hlt : B₁.totalDegree < m := by
          rw [← h, hB₁, totalDegree_mul_of_isDomain hc0 hB₁0]
          omega
        obtain ⟨A', B', hB', hrel', heq⟩ := ih _ hlt A₁ B₁ hB₁0 rfl
        refine ⟨A', B', hB', hrel', ?_⟩
        rw [hB₁, hA₁]
        linear_combination c * heq

variable (Fr : RittFrame K L)

theorem aeval_injective_of_independent {u : L}
    (hind : AlgebraicIndependent K (Fr.jetFamily u n)) :
    Function.Injective (aeval (Fr.jetFamily u n) : MvPolynomial (Fin n) K →ₐ[K] L) := hind

/-- **Reduced representation.**  An element of the jet field is a reduced fraction of polynomials
in the jets. -/
theorem exists_reduced_fraction_of_mem_jetPrefixField [DecidableEq K] {u : L}
    (hind : AlgebraicIndependent K (Fr.jetFamily u n)) {y : L}
    (hy : y ∈ Fr.jetPrefixField u n) :
    ∃ A B : MvPolynomial (Fin n) K, B ≠ 0 ∧ IsRelPrime A B ∧
      y * aeval (Fr.jetFamily u n) B = aeval (Fr.jetFamily u n) A := by
  rw [jetPrefixField, IntermediateField.mem_adjoin_iff_div] at hy
  obtain ⟨r, hr, s, hs, rfl⟩ := hy
  obtain ⟨A, rfl⟩ := Fr.exists_mvPolynomial_of_mem_jetPrefixRing u n hr
  obtain ⟨B, rfl⟩ := Fr.exists_mvPolynomial_of_mem_jetPrefixRing u n hs
  by_cases hB : B = 0
  · refine ⟨0, 1, one_ne_zero, isRelPrime_zero_left.mpr isUnit_one, ?_⟩
    subst hB
    simp
  · obtain ⟨A', B', hB', hrel, heq⟩ := exists_reduced_polynomial_fraction A B hB
    refine ⟨A', B', hB', hrel, ?_⟩
    have hBu : aeval (Fr.jetFamily u n) B ≠ 0 := fun h0 =>
      hB (Fr.aeval_injective_of_independent hind (by rw [h0, map_zero]))
    have := congrArg (aeval (Fr.jetFamily u n)) heq
    rw [map_mul, map_mul] at this
    rw [div_mul_eq_mul_div, div_eq_iff hBu]
    exact this.symm

/-- **The reduced denominator divides every denominator.** -/
theorem dvd_of_denominator {u : L} (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {y : L} {A B : MvPolynomial (Fin n) K} (hrel : IsRelPrime A B)
    (hAB : y * aeval (Fr.jetFamily u n) B = aeval (Fr.jetFamily u n) A)
    {P Q : MvPolynomial (Fin n) K}
    (hPQ : aeval (Fr.jetFamily u n) P * y = aeval (Fr.jetFamily u n) Q) : B ∣ P := by
  have h : P * A = Q * B := by
    refine Fr.aeval_injective_of_independent hind ?_
    rw [map_mul, map_mul, ← hAB, ← hPQ]
    ring
  exact hrel.symm.dvd_of_dvd_mul_right ⟨Q, by rw [h, mul_comm]⟩

/-- **An affinely moving element has an eigen-denominator.**  If `σ y = μ·y + t` with `t` a
polynomial in the jets, the reduced denominator of `y` is a shift eigenvector of the polynomial
tower: `towerShift B = μ'·B`. -/
theorem towerShift_denominator {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {y : L} {A B : MvPolynomial (Fin n) K} (hB : B ≠ 0) (hrel : IsRelPrime A B)
    (hAB : y * aeval (Fr.jetFamily u n) B = aeval (Fr.jetFamily u n) A)
    {μ : K} (hμ : μ ≠ 0) {T : MvPolynomial (Fin n) K}
    (hσy : Fr.σ y = algebraMap K L μ * y + aeval (Fr.jetFamily u n) T) :
    ∃ μ' : K, Fr.towerShift b n B = C μ' * B := by
  have hj : (fun j : Fin n => Fr.d^[(j : ℕ)] u) = Fr.jetFamily u n := rfl
  have hshift : ∀ P : MvPolynomial (Fin n) K,
      aeval (Fr.jetFamily u n) (Fr.towerShift b n P) = Fr.σ (aeval (Fr.jetFamily u n) P) := by
    intro P
    rw [← hj]
    exact Fr.aeval_towerShift hu n P
  -- the shifted denominator is a denominator
  have hden : aeval (Fr.jetFamily u n) (C μ * Fr.towerShift b n B) * y
      = aeval (Fr.jetFamily u n) (Fr.towerShift b n A - Fr.towerShift b n B * T) := by
    have h := congrArg Fr.σ hAB
    rw [map_mul, hσy, ← hshift, ← hshift] at h
    rw [map_mul, aeval_C, map_sub, map_mul, ← h]
    ring
  obtain ⟨Q, hQ⟩ := Fr.dvd_of_denominator hind hrel hAB hden
  obtain ⟨W, d, hBW, hd, hdW⟩ := exists_top_weight hB
  have hQ' : Fr.towerShift b n B = B * (C μ⁻¹ * Q) := by
    have h := congrArg (fun P => C μ⁻¹ * P) hQ
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hμ, C_1, one_mul] at h
    rw [h]
    ring
  have hwle : WLe n (B * (C μ⁻¹ * Q)) W := hQ' ▸ Fr.wLe_towerShift b hBW
  have hQ0 := eq_C_of_wLe_zero' (wLe_zero_of_wLe_mul hBW hd hdW hwle)
  refine ⟨coeff 0 (C μ⁻¹ * Q), ?_⟩
  rw [hQ', ← hQ0]
  ring

/-- **The eigen-denominator is a power of the eigen-coordinate.** -/
theorem aeval_eq_of_towerShift_eigen {u v : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {B : MvPolynomial (Fin n) K} (hB : B ≠ 0) {μ' : K}
    (hBμ : Fr.towerShift b n B = C μ' * B) :
    ∃ (k : K) (W : ℕ), k ≠ 0 ∧ aeval (Fr.jetFamily u n) B = algebraMap K L k * v ^ W := by
  obtain ⟨W, d, hBW, hd, hdW⟩ := exists_top_weight hB
  have hf : coeff d B ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have htop := Fr.coeff_towerShift_of_top b hBW hdW
  rw [hBμ, coeff_C_mul] at htop
  have hj : (fun j : Fin n => Fr.d^[(j : ℕ)] u) = Fr.jetFamily u n := rfl
  have hσB : Fr.σ (aeval (Fr.jetFamily u n) B)
      = algebraMap K L μ' * aeval (Fr.jetFamily u n) B := by
    rw [← hj, ← Fr.aeval_towerShift hu n B, hBμ, map_mul, aeval_C]
  set z := aeval (Fr.jetFamily u n) B / (algebraMap K L (coeff d B) * v ^ W) with hz
  have hρW : algebraMap K L (Fr.ρ ^ W)⁻¹ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (inv_ne_zero (pow_ne_zero _ Fr.ρ_ne))
  have hfL : algebraMap K L (coeff d B) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hf
  have hψ : Fr.ψ (coeff d B) = μ' * coeff d B * Fr.ρ ^ W := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ Fr.ρ_ne)] at htop
    exact htop.symm
  have hμ' : μ' ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hψ
    exact hf (Fr.ψ.injective (by rw [hψ, map_zero]))
  have hμL : algebraMap K L μ' ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hμ'
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne
  have hfix : Fr.σ z = z := by
    rw [hz, map_div₀, hσB, map_mul, map_pow, hv, Fr.comp, hψ, map_mul, map_mul, map_pow,
      map_inv₀, mul_pow, inv_pow]
    field_simp
  obtain ⟨a, ha⟩ := Fr.fixed z hfix
  have hBu : aeval (Fr.jetFamily u n) B ≠ 0 := fun h0 =>
    hB (Fr.aeval_injective_of_independent hind (by rw [h0, map_zero]))
  have hvW : v ^ W ≠ 0 := pow_ne_zero _ hv0
  refine ⟨a * coeff d B, W, ?_, ?_⟩
  · intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [h, map_zero, hz] at ha
      exact hBu (by
        have := ha.symm
        rw [div_eq_zero_iff] at this
        rcases this with h' | h'
        · exact h'
        · exact absurd h' (mul_ne_zero hfL hvW))
    · exact hf h
  · rw [map_mul, ha, hz]
    field_simp

end RittFrame

end

end GaloisForLFunctions.HTGeometry
