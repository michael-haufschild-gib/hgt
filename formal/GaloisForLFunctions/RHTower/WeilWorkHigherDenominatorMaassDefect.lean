import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorEndpointResidues

/-!
# Endpoint cancellation in the actual Maass function

The original cubic datum gives infinitely many deficits or a Maass axis defect
consisting only of nonzero interior logarithmic modes. Both endpoint residues
are cancelled with the existing factor-four normalization.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry
open RHTower.MaassBesselSeries RHTower.MaassConverseLevelOne RHTower.MaassThetaMellin

namespace RHTower.WeilHigherDenominator

private lemma sign_mul_self {E : ℂ → ℂ} {ε : ℂ} (hE1 : E 1 ≠ 0)
    (hfe : ∀ s, E (1 - s) = ε * E s) : ε * ε = 1 := by
  have h₀ : E 1 = ε * E 0 := by simpa using hfe 0
  have h₁ : E 0 = ε * E 1 := by simpa using hfe 1
  apply mul_right_cancel₀ hE1
  calc
    ε * ε * E 1 = ε * E 0 := by rw [h₁]; ring
    _ = 1 * E 1 := by rw [← h₀, one_mul]

private lemma sum_degreeTwoPoleSet {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    (F : ℂ → ℂ) :
    ∑ ρ ∈ degreeTwoPoleSet P, F ρ = (∑ ρ ∈ P.roots.toFinset, F ρ) + F 0 + F 1 := by
  classical
  have hdisj : Disjoint P.roots.toFinset ({0, 1} : Finset ℂ) := by
    apply Finset.disjoint_left.mpr
    intro ρ hρ he
    have hx := deficitPolynomial_root_xi_zero P hord
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hρ))
    rcases Finset.mem_insert.mp he with rfl | he
    · norm_num [xi_zero] at hx
    · have hρ1 : ρ = 1 := Finset.mem_singleton.mp he
      norm_num [hρ1, xi_one] at hx
  rw [degreeTwoPoleSet, Finset.sum_union hdisj]
  simp [add_assoc]

private lemma maass_axis_of_theta_packet {g : ℕ → ℂ} {ε a b : ℂ}
    (hε : ε * ε = 1) (Z : Finset ℂ) (Q : ℂ → Polynomial ℂ)
    (hθ : ∀ x : ℝ, 0 < x →
      kTheta g x - ε * ((x : ℂ) ^ (-1 : ℂ) * kTheta g x⁻¹) =
        (1 / 4 : ℂ) * ((∑ ρ ∈ Z, (x : ℂ) ^ (-ρ) * (Q ρ).eval (Real.log x : ℂ)) +
          (x : ℂ) ^ (-1 : ℂ) * (b - a * (Real.log x : ℂ)) - ε * (b + a * (Real.log x : ℂ))))
    {x : ℝ} (hx : 0 < x) :
    maassFun g (ε * a) (ε * b) ((x : ℂ) * I) -
        ε * maassFun g (ε * a) (ε * b) (((x⁻¹ : ℝ) : ℂ) * I) =
      ∑ ρ ∈ Z, (x : ℂ) ^ ((1 / 2 : ℂ) - ρ) * (Q ρ).eval (Real.log x : ℂ) := by
  let r : ℝ := x ^ (1 / 2 : ℝ)
  have hsq : (x⁻¹ : ℝ) ^ (1 / 2 : ℝ) = r⁻¹ := by
    rw [← one_div x, Real.div_rpow zero_le_one hx.le, Real.one_rpow, one_div]
  have hr2 : r ^ 2 = x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
  have hr2c : (r : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast hr2
  have hrc : (r : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
    dsimp [r]
    rw [ofReal_cpow hx.le]
    norm_num
  have hpack : (∑ ρ ∈ Z, (x : ℂ) ^ ((1 / 2 : ℂ) - ρ) * (Q ρ).eval (Real.log x : ℂ)) =
      (r : ℂ) * ∑ ρ ∈ Z, (x : ℂ) ^ (-ρ) * (Q ρ).eval (Real.log x : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [hrc, sub_eq_add_neg, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    ring
  have hθx := eq_add_of_sub_eq (hθ x hx)
  rw [Complex.cpow_neg_one] at hθx
  rw [maassFun, maassFun, cosSeries_axis, cosSeries_axis, constTerm_axis, constTerm_axis,
    hsq, Real.log_inv, hpack]
  change 4 * ((r : ℂ) * kTheta g x) + (r : ℂ) * (ε * b + ε * a * (Real.log x : ℂ)) -
      ε * (4 * (((r⁻¹ : ℝ) : ℂ) * kTheta g x⁻¹) + ((r⁻¹ : ℝ) : ℂ) *
        (ε * b + ε * a * (-Real.log x : ℝ))) = _
  rw [hθx]
  push_cast
  rw [← hr2c]
  have hε2 : ε ^ 2 = 1 := by simpa only [pow_two] using hε
  field_simp
  linear_combination (a * (Real.log x : ℂ) - b) * hε2

/-- The actual quotient's Maass function has exactly the interior polynomial axis packet. -/
theorem degreeTwoQuotient_maass_axis_defect {g : ℕ → ℂ} {E H : ℂ → ℂ} {ε : ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hfe : ∀ s, E (1 - s) = ε * E s) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    (Q : ℂ → Polynomial ℂ)
    (hrep : ∀ ρ : ℂ, ∀ x : ℝ, 0 < x →
      laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) ρ (-1) =
        (x : ℂ) ^ (-ρ) * (Q ρ).eval (Real.log x : ℂ))
    {x : ℝ} (hx : 0 < x) :
    maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
        (ε * deriv (degreeTwoEndpointNumerator E) 1) ((x : ℂ) * I) -
      ε * maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
        (ε * deriv (degreeTwoEndpointNumerator E) 1) (((x⁻¹ : ℝ) : ℂ) * I) =
      ∑ ρ ∈ P.roots.toFinset, (x : ℂ) ^ ((1 / 2 : ℂ) - ρ) * (Q ρ).eval (Real.log x : ℂ) := by
  apply maass_axis_of_theta_packet (sign_mul_self hE1 hfe) P.roots.toFinset Q (x := x) (hx := hx)
  intro y hy
  rw [degreeTwoQuotient_theta_defect hD hfe P hP hH hHfinite hfac hord hy,
    sum_degreeTwoPoleSet P hord,
    poleClearedDegreeTwoCompletion_residue_zero hD.entire hH hfe P hfac hord hy,
    poleClearedDegreeTwoCompletion_residue_one hD.entire hH P hfac hord hy]
  have hsum := Finset.sum_congr (s₁ := P.roots.toFinset) rfl fun ρ _ => hrep ρ y hy
  rw [hsum]
  ring

/-- No endpoint, residue, sign-square or mode-realization premise is added to the original datum. -/
theorem degreeThree_infiniteDeficits_or_maassDefect {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ) (ε : ℂ) (Q : ℂ → Polynomial ℂ),
        P.Monic ∧ ‖ε‖ = 1 ∧ (∀ s, E (1 - s) = ε * E s) ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        (∀ ρ ∈ P.roots.toFinset, 0 < ρ.re ∧ ρ.re < 1 ∧ Q ρ ≠ 0) ∧
        ∀ x : ℝ, 0 < x →
          maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
              (ε * deriv (degreeTwoEndpointNumerator E) 1) ((x : ℂ) * I) -
            ε * maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
              (ε * deriv (degreeTwoEndpointNumerator E) 1) (((x⁻¹ : ℝ) : ℂ) * I) =
            ∑ ρ ∈ P.roots.toFinset, (x : ℂ) ^ ((1 / 2 : ℂ) - ρ) * (Q ρ).eval (Real.log x : ℂ) := by
  rcases degreeThree_infiniteDeficits_or_poleCleared hD hE1 with hi | ⟨P, H, hm, _, ho, hd, hg, h₁, hf⟩
  · exact Or.inl hi
  · obtain ⟨ε, hε, he⟩ := hD.exists_sign
    obtain ⟨Q, hrep, hzero⟩ := exists_poleCleared_residue_polynomials P hd
    refine Or.inr ⟨P, H, ε, Q, hm, hε, he, ho, hd, hg, h₁, hf, ?_, ?_⟩
    · intro ρ hρ
      have hp : P.eval ρ = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hρ)
      have hr := deficitPolynomial_root_re_mem_Ioo P ho hp
      refine ⟨hr.1, hr.2, ?_⟩
      intro hq
      exact (not_le_of_gt (poleClearedDegreeTwoCompletion_order_neg_at_root
        hD.entire hE1 hd h₁ P hf ho hp)) ((hzero ρ).mp hq)
    · exact fun x hx => degreeTwoQuotient_maass_axis_defect hD hE1 he P hm.ne_zero hd hg hf ho Q hrep hx

end RHTower.WeilHigherDenominator
