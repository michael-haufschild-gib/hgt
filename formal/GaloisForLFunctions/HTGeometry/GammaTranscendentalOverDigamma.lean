import GaloisForLFunctions.HTGeometry.LinePolyGrowth

/-!
# Gamma is transcendental over the digamma field

Every value of a jet polynomial in `ψ, ψ′, …` with rational coefficients has polynomial growth on a
vertical line, while `Γ` beats every power downwards there.  So in a polynomial relation for `Γ` over
those values the constant term would be flat, hence zero by the line form of the flat elimination;
`Γ` is a unit in the germ ring, so the relation divides and the argument repeats.

Therefore `Γ` satisfies no polynomial relation over the digamma field — eq. (22)–(23) of the
projective boundary law, with the vertical decay in place of the scaling automorphism.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The germ of the Gamma function on the half-plane. -/
noncomputable def gammaGerm (σ₀ : ℝ) : HalfPlaneGerm σ₀ :=
  ((fun s : ℂ => Complex.Gamma s : ℂ → ℂ) : HalfPlaneGerm σ₀)

/-- Gamma has no zeros, so its germ is a unit. -/
theorem isUnit_gammaGerm (σ₀ : ℝ) : IsUnit (gammaGerm σ₀) := by
  refine IsUnit.of_mul_eq_one ((fun s : ℂ => (Complex.Gamma s)⁻¹ : ℂ → ℂ) : HalfPlaneGerm σ₀) ?_
  rw [gammaGerm, ← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_off_poles σ₀] with s hs
  exact mul_inv_cancel₀ (Complex.Gamma_ne_zero hs)

/-- Polynomial growth only depends on the germ. -/
theorem HasPolyGrowth.congr_germ {σ₀ : ℝ} {A B : ℂ → ℂ}
    (h : A =ᶠ[halfPlaneUpper σ₀] B) (hA : HasPolyGrowth σ₀ A) : HasPolyGrowth σ₀ B := by
  intro σ hσ
  obtain ⟨M, C, hC, hb⟩ := hA σ hσ
  refine ⟨M, C, hC, ?_⟩
  filter_upwards [hb, eventually_line_of_halfPlaneUpper h hσ] with t ht hEq
  rw [← hEq]
  exact ht

/-- A germ has polynomial growth when one — equivalently every — representative has. -/
def HasPolyGrowthGerm (σ₀ : ℝ) (g : HalfPlaneGerm σ₀) : Prop :=
  Quotient.liftOn g (HasPolyGrowth σ₀) fun _A _B h =>
    propext ⟨fun hA => hA.congr_germ h, fun hB => hB.congr_germ h.symm⟩

@[simp] theorem hasPolyGrowthGerm_coe {σ₀ : ℝ} (A : ℂ → ℂ) :
    HasPolyGrowthGerm σ₀ (↑A : HalfPlaneGerm σ₀) ↔ HasPolyGrowth σ₀ A := Iff.rfl

theorem HasPolyGrowthGerm.add {σ₀ : ℝ} {g h : HalfPlaneGerm σ₀} (hg : HasPolyGrowthGerm σ₀ g)
    (hh : HasPolyGrowthGerm σ₀ h) : HasPolyGrowthGerm σ₀ (g + h) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    induction h using Filter.Germ.inductionOn with
    | h B => exact HasPolyGrowth.add hg hh

theorem HasPolyGrowthGerm.mul {σ₀ : ℝ} {g h : HalfPlaneGerm σ₀} (hg : HasPolyGrowthGerm σ₀ g)
    (hh : HasPolyGrowthGerm σ₀ h) : HasPolyGrowthGerm σ₀ (g * h) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    induction h using Filter.Germ.inductionOn with
    | h B => exact HasPolyGrowth.mul hg hh

theorem hasPolyGrowthGerm_ratGerm {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (k : RatFunc ℂ) :
    HasPolyGrowthGerm σ₀ (ratGerm σ₀ k) := by
  rw [ratGerm_eq_div]
  exact hasPolyGrowth_ratFunc hσ₀ k

theorem hasPolyGrowthGerm_digammaJetGerm {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (j : ℕ) :
    HasPolyGrowthGerm σ₀ (digammaJetGerm σ₀ j) :=
  hasPolyGrowth_digammaJet hσ₀ j

theorem hasPolyGrowthGerm_gammaGerm {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    HasPolyGrowthGerm σ₀ (gammaGerm σ₀) := by
  show HasPolyGrowth σ₀ (fun s : ℂ => Complex.Gamma s)
  refine hasPolyGrowth_of_eventually_le (C := 1) zero_le_one (fun σ hσ => ?_)
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  have h : Tendsto (fun t : ℝ => ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
      atTop (nhds 0) := by
    have := (tendsto_pow_mul_Gamma_vertical hσ0 0).norm
    simpa using this
  have hlt : ∀ᶠ t : ℝ in atTop,
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ < 1 :=
    h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt] with t ht using ht.le

/-- Every value of a jet polynomial at the digamma jets has polynomial growth. -/
theorem hasPolyGrowthGerm_digammaJetEval {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {m : ℕ}
    (G : MvPolynomial (Fin m) (RatFunc ℂ)) :
    HasPolyGrowthGerm σ₀ (digammaJetEval σ₀ m G) := by
  refine MvPolynomial.induction_on (motive := fun H => HasPolyGrowthGerm σ₀ (digammaJetEval σ₀ m H)) G
    (fun k => ?_) (fun p q hp hq => ?_) (fun p j hp => ?_)
  · rw [digammaJetEval_C]
    exact hasPolyGrowthGerm_ratGerm hσ₀.le k
  · rw [map_add]
    exact hp.add hq
  · rw [map_mul, digammaJetEval_X]
    exact hp.mul (hasPolyGrowthGerm_digammaJetGerm hσ₀ (j : ℕ))

/-- **Gamma flattens polynomial growth.**  The product of the Gamma germ with a germ of polynomial
growth is flat on every vertical line. -/
theorem isVertFlatGerm_gammaGerm_mul {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {g : HalfPlaneGerm σ₀}
    (hg : HasPolyGrowthGerm σ₀ g) : IsVertFlatGerm σ₀ (gammaGerm σ₀ * g) := by
  induction g using Filter.Germ.inductionOn with
  | h B =>
    have hB : HasPolyGrowth σ₀ B := hg
    show IsVertFlatGerm σ₀ ((fun s : ℂ => Complex.Gamma s : ℂ → ℂ) * (↑B : HalfPlaneGerm σ₀))
    rw [← Filter.Germ.coe_mul]
    exact isVertFlat_gamma_mul hσ₀ hB

/-- The zero germ is flat. -/
theorem isVertFlatGerm_zero (σ₀ : ℝ) : IsVertFlatGerm σ₀ (0 : HalfPlaneGerm σ₀) := by
  show IsVertFlatGerm σ₀ ((0 : ℂ → ℂ) : HalfPlaneGerm σ₀)
  intro N σ hσ
  simp

theorem hasPolyGrowthGerm_zero (σ₀ : ℝ) : HasPolyGrowthGerm σ₀ (0 : HalfPlaneGerm σ₀) := by
  show HasPolyGrowth σ₀ ((0 : ℂ → ℂ))
  intro σ hσ
  exact ⟨0, 0, le_rfl, by simp⟩

theorem hasPolyGrowthGerm_one (σ₀ : ℝ) : HasPolyGrowthGerm σ₀ (1 : HalfPlaneGerm σ₀) := by
  show HasPolyGrowth σ₀ ((1 : ℂ → ℂ))
  intro σ hσ
  exact ⟨0, 1, zero_le_one, by simp⟩

theorem hasPolyGrowthGerm_gammaGerm_pow {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (k : ℕ) :
    HasPolyGrowthGerm σ₀ (gammaGerm σ₀ ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact hasPolyGrowthGerm_one σ₀
  | succ p hp =>
    rw [pow_succ]
    exact hp.mul (hasPolyGrowthGerm_gammaGerm hσ₀)

/-- A finite Gamma-polynomial with digamma-jet coefficients has polynomial growth. -/
theorem hasPolyGrowthGerm_gammaSum {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {m : ℕ}
    (P : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)) (n : ℕ) :
    HasPolyGrowthGerm σ₀
      (∑ k ∈ Finset.range n, digammaJetEval σ₀ m (P k) * gammaGerm σ₀ ^ k) := by
  refine Finset.sum_induction _ (HasPolyGrowthGerm σ₀) (fun a b ha hb => ha.add hb)
    (hasPolyGrowthGerm_zero σ₀) (fun k _ => ?_)
  exact (hasPolyGrowthGerm_digammaJetEval hσ₀ (P k)).mul (hasPolyGrowthGerm_gammaGerm_pow hσ₀ k)

/-- **Gamma is transcendental over the digamma field.**  A polynomial relation for the Gamma germ
whose coefficients are values of jet polynomials in the digamma jets has all coefficients zero. -/
theorem digammaJet_gamma_independent {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {m : ℕ} :
    ∀ (d : ℕ) (P : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)),
      (∑ i ∈ Finset.range d, digammaJetEval σ₀ m (P i) * gammaGerm σ₀ ^ i) = 0 →
      ∀ i < d, P i = 0 := by
  intro d
  induction d with
  | zero => intro P _ i hi; exact absurd hi (by omega)
  | succ n ih =>
    intro P hrel i hi
    set S : HalfPlaneGerm σ₀ :=
      ∑ k ∈ Finset.range n, digammaJetEval σ₀ m (P (k + 1)) * gammaGerm σ₀ ^ k with hS
    have hsplit : digammaJetEval σ₀ m (P 0) + gammaGerm σ₀ * S = 0 := by
      rw [← hrel, Finset.sum_range_succ']
      have hterm : ∀ k ∈ Finset.range n,
          digammaJetEval σ₀ m (P (k + 1)) * gammaGerm σ₀ ^ (k + 1)
            = gammaGerm σ₀ * (digammaJetEval σ₀ m (P (k + 1)) * gammaGerm σ₀ ^ k) := by
        intro k _
        rw [pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hS, pow_zero, mul_one]
      ring
    have hSgrowth : HasPolyGrowthGerm σ₀ S := by
      rw [hS]
      exact hasPolyGrowthGerm_gammaSum hσ₀ (fun k => P (k + 1)) n
    have hzero0 : P 0 = 0 := by
      by_contra hne
      refine not_isVertFlatGerm_digammaJetEval hσ₀.le hne ?_
      have heq : digammaJetEval σ₀ m (P 0) = 0 - gammaGerm σ₀ * S := by
        linear_combination hsplit
      rw [heq]
      exact IsVertFlatGerm.sub (isVertFlatGerm_zero σ₀)
        (isVertFlatGerm_gammaGerm_mul hσ₀ hSgrowth)
    have hS0 : S = 0 := by
      have hmul : gammaGerm σ₀ * S = 0 := by
        rw [hzero0] at hsplit
        simpa using hsplit
      obtain ⟨u, hu⟩ := isUnit_gammaGerm σ₀
      have hcancel : (↑u⁻¹ : HalfPlaneGerm σ₀) * (gammaGerm σ₀ * S) = 0 := by
        rw [hmul, mul_zero]
      rw [← mul_assoc, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at hcancel
      exact hcancel
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact hzero0
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      exact ih (fun k => P (k + 1)) hS0 k (by omega)

/-! ### The lowest Gamma power dominates -/

/-- Line flatness survives multiplication by a function of polynomial growth. -/
theorem IsVertFlat.mul_hasPolyGrowth {σ₀ : ℝ} {A B : ℂ → ℂ} (hA : IsVertFlat σ₀ A)
    (hB : HasPolyGrowth σ₀ B) : IsVertFlat σ₀ (fun s => A s * B s) := by
  intro N σ hσ
  obtain ⟨M, C, hC, hb⟩ := hB σ hσ
  have hA' := (hA (N + M) σ hσ).const_mul C
  rw [mul_zero] at hA'
  refine squeeze_zero' ?_ ?_ hA'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with t hbt ht
  have hAnn : (0 : ℝ) ≤ ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  calc t ^ N * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) * B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = t ^ N * (‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by rw [norm_mul]
    _ ≤ t ^ N * (‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (C * t ^ M)) := by
        have := mul_le_mul_of_nonneg_left hbt hAnn
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * (t ^ (N + M) * ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [pow_add]
        ring

theorem IsVertFlatGerm.mul_hasPolyGrowthGerm {σ₀ : ℝ} {g h : HalfPlaneGerm σ₀}
    (hg : IsVertFlatGerm σ₀ g) (hh : HasPolyGrowthGerm σ₀ h) : IsVertFlatGerm σ₀ (g * h) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    induction h using Filter.Germ.inductionOn with
    | h B => exact IsVertFlat.mul_hasPolyGrowth hg hh

/-- A Gamma polynomial without constant term is flat: every positive power of `Γ` beats the
polynomial growth of its coefficient. -/
theorem isVertFlatGerm_gammaSum_succ {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {m : ℕ}
    (P : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)) (n : ℕ) :
    IsVertFlatGerm σ₀
      (∑ k ∈ Finset.range n, digammaJetEval σ₀ m (P k) * gammaGerm σ₀ ^ (k + 1)) := by
  have hrw : (∑ k ∈ Finset.range n, digammaJetEval σ₀ m (P k) * gammaGerm σ₀ ^ (k + 1))
      = gammaGerm σ₀ * ∑ k ∈ Finset.range n, digammaJetEval σ₀ m (P k) * gammaGerm σ₀ ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]
    ring
  rw [hrw]
  exact isVertFlatGerm_gammaGerm_mul hσ₀ (hasPolyGrowthGerm_gammaSum hσ₀ P n)

/-- **Eq. (25): the lowest Gamma power dominates.**  A Gamma polynomial with digamma-jet
coefficients differs from its constant term by a flat germ, so after normalizing by the lowest
occurring power the limit datum is the coefficient of that power. -/
theorem isVertFlatGerm_gammaSum_sub_const {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {m : ℕ}
    (P : ℕ → MvPolynomial (Fin m) (RatFunc ℂ)) (d : ℕ) :
    IsVertFlatGerm σ₀
      ((∑ i ∈ Finset.range (d + 1), digammaJetEval σ₀ m (P i) * gammaGerm σ₀ ^ i)
        - digammaJetEval σ₀ m (P 0)) := by
  have hsplit : (∑ i ∈ Finset.range (d + 1), digammaJetEval σ₀ m (P i) * gammaGerm σ₀ ^ i)
      - digammaJetEval σ₀ m (P 0)
      = ∑ k ∈ Finset.range d, digammaJetEval σ₀ m (P (k + 1)) * gammaGerm σ₀ ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    simp [pow_zero]
  rw [hsplit]
  exact isVertFlatGerm_gammaSum_succ hσ₀ (fun k => P (k + 1)) d

end GaloisForLFunctions
