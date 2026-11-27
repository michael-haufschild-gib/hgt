import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.MatchgateRankThreeEscape

/-! # Matchgate `Spin(2N)` synthesis and hidden rank-`2` matchgate survival tube

This module establishes the exact `choose(2N, 2)` two-qubit compilation of locally rotated
matchgate chains and constructs the hidden rotated matchgate survival tube inside
`allCoordStrongEvent ∩ bondRankTwoEvent` on the `1`D `N = n + 2` qubit Pauli chain:

1. **Full `2N`-mode Jordan-Wigner Clifford representation and exact `choose(2N, 2)` compilation:**
   - `realizes_choose_twoN_of_matchgateChain`, `realizes_conj_prodLocalMatrix`, &
     `realizes_choose_twoN_of_locallyRotatedMatchgate`: every `(5N - 4)`-parameter
     `isMatchgateChainLabel` chain Hamiltonian — and every `U(2)^⊗N` local gauge rotation thereof —
     compiles **exactly for all `t ∈ ℝ`** in `choose(2N, 2) = (n + 2) * (2 * n + 3)` two-qubit gates
     via `fullJWMajorana n`, `exists_adjGivens_prod_eq_of_specialOrthogonal (2 * (n + 2))`, and
     `eq_scalar_one_of_mem_evenClifford_commutant`.
2. **Hidden rotated matchgate survival tube inside `allCoordStrongEvent ∩ bondRankTwoEvent`:**
   - `gaussian_hiddenMatchgate_rankTwo_tube_tail`: conjugating a rank-`2` matchgate box by
     `pythUnitary^{⊗N}` embeds a survival tube **strictly inside
     `allCoordStrongEvent (k + 1) η ∩ bondRankTwoEvent (k + 1) η`** with `pathPauliDisorderLaw`
     probability `≥ c_MG(k, η) * T ^ -(7 * k + 16)` (`7N - 5` weak coordinates) on which
     `T < tenthPlateauOnset H s` for all `(k + 3) * (2 * k + 5) ≤ s ≤ P` despite maximally
     projective simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2` return excision. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-! ## Section 1: Full `2N`-mode Jordan-Wigner Clifford representation & `choose(2N, 2)` compilation -/

section AbstractCliffordHelpers

private theorem skew_square_exp' {A : Type*} [CStarAlgebra A] {X : A} (hX : X * X = -1) (θ : ℝ) :
    NormedSpace.exp ((θ : ℂ) • X) =
      (Real.cos θ : ℂ) • (1 : A) + (Real.sin θ : ℂ) • X := by
  have hsq : ((θ : ℂ) • X) * ((θ : ℂ) • X) = (-((θ : ℂ) ^ (2 : ℕ))) • (1 : A) := by
    rw [smul_mul_smul_comm, hX, smul_neg, ← neg_smul, pow_two]
  rw [_root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one _ θ hsq, smul_smul]
  have hsin : Real.sinc θ * θ = Real.sin θ := by
    by_cases h : θ = 0
    · simp only [h, mul_zero, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero h, div_mul_cancel₀ _ h]
  rw [← Complex.ofReal_mul, hsin]

private theorem exp_skewPair_star_eq' {A : Type*} [CStarAlgebra A] {γ₁ γ₂ : A}
    (hst₁ : star γ₁ = γ₁) (hst₂ : star γ₂ = γ₂) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁)) (θ : ℝ) :
    star (NormedSpace.exp ((θ : ℂ) • (γ₁ * γ₂))) =
      NormedSpace.exp (((-θ : ℝ) : ℂ) • (γ₁ * γ₂)) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  rw [NormedSpace.star_exp, star_smul, star_mul, hst₂, hst₁]
  have hst_prod : γ₂ * γ₁ = -(γ₁ * γ₂) := by rw [← neg_neg (γ₂ * γ₁), ← hanti]
  rw [hst_prod, Complex.star_def, Complex.conj_ofReal, smul_neg, Complex.ofReal_neg, neg_smul]

private theorem exp_skewPair_conj' {A : Type*} [CStarAlgebra A] {γ₁ γ₂ : A}
    (h₁ : γ₁ * γ₁ = 1) (h₂ : γ₂ * γ₂ = 1)
    (hst₁ : star γ₁ = γ₁) (hst₂ : star γ₂ = γ₂) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁)) (φ : ℝ) :
    let U := NormedSpace.exp (((φ / 2 : ℝ) : ℂ) • (γ₁ * γ₂))
    U * γ₁ * star U = (Real.cos φ : ℂ) • γ₁ + ((-Real.sin φ : ℝ) : ℂ) • γ₂ ∧
    U * γ₂ * star U = (Real.sin φ : ℂ) • γ₁ + (Real.cos φ : ℂ) • γ₂ ∧
    ∀ γ₃ : A, γ₁ * γ₃ = -(γ₃ * γ₁) → γ₂ * γ₃ = -(γ₃ * γ₂) → U * γ₃ * star U = γ₃ := by
  intro U
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let X := γ₁ * γ₂
  have hX₁ : X * γ₁ = -γ₂ := by dsimp [X]; rw [hanti, neg_mul, mul_assoc, h₁, mul_one]
  have h₁X : γ₁ * X = γ₂ := by dsimp [X]; rw [← mul_assoc, h₁, one_mul]
  have hX₂ : X * γ₂ = γ₁ := by dsimp [X]; rw [mul_assoc, h₂, mul_one]
  have h₂X : γ₂ * X = -γ₁ := by
    dsimp [X]; rw [← mul_assoc]
    have h21 : γ₂ * γ₁ = -(γ₁ * γ₂) := by rw [← neg_neg (γ₂ * γ₁), ← hanti]
    rw [h21, neg_mul, mul_assoc, h₂, mul_one]
  have hX_sq : X * X = -1 := by dsimp [X]; rw [← mul_assoc, hX₁, neg_mul, h₂]
  have hU_exp : U = (Real.cos (φ / 2) : ℂ) • (1 : A) + (Real.sin (φ / 2) : ℂ) • X :=
    skew_square_exp' hX_sq (φ / 2)
  have hstU : star U = NormedSpace.exp (((-(φ / 2) : ℝ) : ℂ) • X) :=
    exp_skewPair_star_eq' hst₁ hst₂ hanti (φ / 2)
  have hstU_exp : star U =
      (Real.cos (φ / 2) : ℂ) • (1 : A) + (-(Real.sin (φ / 2) : ℂ)) • X := by
    rw [hstU, skew_square_exp' hX_sq (-(φ / 2)), Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  have hc_double : Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 = Real.cos φ := by
    have h2 : φ = 2 * (φ / 2) := by ring
    conv_rhs => rw [h2, Real.cos_two_mul]
    linarith only [Real.sin_sq_add_cos_sq (φ / 2)]
  have hs_double : 2 * Real.sin (φ / 2) * Real.cos (φ / 2) = Real.sin φ := by
    rw [← Real.sin_two_mul, show 2 * (φ / 2) = φ by ring]
  let c : ℂ := (Real.cos (φ / 2) : ℂ)
  let s : ℂ := (Real.sin (φ / 2) : ℂ)
  have hc_c : c * c - s * s = (Real.cos φ : ℂ) := by
    dsimp [c, s]; exact_mod_cast (by simpa [pow_two] using hc_double)
  have hs_c : 2 * s * c = (Real.sin φ : ℂ) := by
    dsimp [c, s]; exact_mod_cast hs_double
  refine ⟨?_, ?_, ?_⟩
  · rw [hstU_exp, hU_exp]
    change (c • (1 : A) + s • X) * γ₁ * (c • (1 : A) + (-s) • X) = _
    have hL : (c • (1 : A) + s • X) * γ₁ = c • γ₁ + (-s) • γ₂ := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hX₁, smul_neg, neg_smul]
    rw [hL, add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, mul_one, h₁X, h₂X, smul_neg]
    rw [Complex.ofReal_neg, ← hc_c, ← hs_c,
      show c * -s = -(s * c) by ring, show -s * c = -(s * c) by ring,
      show -s * -s = s * s by ring, show -(2 * s * c) = -(s * c) + -(s * c) by ring,
      sub_smul, add_smul, neg_smul]
    abel
  · rw [hstU_exp, hU_exp]
    change (c • (1 : A) + s • X) * γ₂ * (c • (1 : A) + (-s) • X) = _
    have hL : (c • (1 : A) + s • X) * γ₂ = c • γ₂ + s • γ₁ := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hX₂]
    rw [hL, add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, mul_one, h₁X, h₂X, smul_neg]
    rw [← hc_c, ← hs_c, show c * -s = -(s * c) by ring,
      show s * -s = -(s * s) by ring, show 2 * s * c = s * c + s * c by ring]
    simp only [sub_smul, add_smul, neg_smul, neg_neg]
    abel
  · intro γ₃ ha₁ ha₂
    have hcommX : Commute X γ₃ := by
      change (γ₁ * γ₂) * γ₃ = γ₃ * (γ₁ * γ₂)
      rw [mul_assoc, ha₂, mul_neg, ← mul_assoc, ha₁, neg_mul, neg_neg, mul_assoc]
    have hcommU : U * γ₃ = γ₃ * U :=
      ((hcommX.smul_left ((φ / 2 : ℝ) : ℂ)).exp_left).eq
    have hU_unit : U * star U = 1 := by
      rw [hstU, ← NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left _).smul_right _)]
      have h0 : ((φ / 2 : ℝ) : ℂ) • X + ((-(φ / 2) : ℝ) : ℂ) • X = 0 := by
        rw [← add_smul, Complex.ofReal_neg, add_neg_cancel, zero_smul]
      rw [h0, NormedSpace.exp_zero]
    rw [hcommU, mul_assoc, hU_unit, mul_one]

private theorem mul_cliffordListProd_toggle' {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a)) (c : Fin m) :
    ∀ (L : List (Fin m)), L.Nodup → c ∈ L → ∀ (f : Fin m → Bool),
      ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        γ c * cliffordListProd γ L f = ε • cliffordListProd γ L (Function.update f c (!f c))
  | [], _, hc, _ => (List.not_mem_nil hc).elim
  | d :: tail, hnd, hc, f => by
      obtain ⟨hd_not, hnd_tail⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hc with rfl | hc_tail
      · have htail_eq : cliffordListProd γ tail (Function.update f c (!f c)) =
            cliffordListProd γ tail f := by
          unfold cliffordListProd; congr 1
          exact List.map_congr_left fun a ha => by
            have hne : a ≠ c := fun h => hd_not (h ▸ ha)
            rw [Function.update_of_ne hne]
        refine ⟨1, Or.inl rfl, ?_⟩
        rw [one_smul]
        change γ c * ((if f c then γ c else 1) * cliffordListProd γ tail f) =
          (if Function.update f c (!f c) c then γ c else 1) *
            cliffordListProd γ tail (Function.update f c (!f c))
        rw [Function.update_self, htail_eq]
        cases f c <;> simp [← mul_assoc, hsq c]
      · have hcd : c ≠ d := fun h => hd_not (h ▸ hc_tail)
        obtain ⟨ε, hε, ih⟩ := mul_cliffordListProd_toggle' hsq hanti c tail hnd_tail hc_tail f
        cases hfd : f d
        · refine ⟨ε, hε, ?_⟩
          change γ c * ((if f d then γ d else 1) * cliffordListProd γ tail f) =
            ε • ((if Function.update f c (!f c) d then γ d else 1) *
              cliffordListProd γ tail (Function.update f c (!f c)))
          rw [Function.update_of_ne hcd.symm, hfd]
          simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
          exact ih
        · refine ⟨-ε, by rcases hε with rfl | rfl <;> [exact Or.inr rfl; exact Or.inl (by norm_num)], ?_⟩
          change γ c * ((if f d then γ d else 1) * cliffordListProd γ tail f) =
            (-ε) • ((if Function.update f c (!f c) d then γ d else 1) *
              cliffordListProd γ tail (Function.update f c (!f c)))
          rw [Function.update_of_ne hcd.symm, hfd]
          simp only [↓reduceIte]
          calc γ c * (γ d * cliffordListProd γ tail f)
              = -(γ d * (γ c * cliffordListProd γ tail f)) := by
                  rw [← mul_assoc, hanti c d hcd, neg_mul, mul_assoc]
            _ = (-ε) • (γ d * cliffordListProd γ tail (Function.update f c (!f c))) := by
                  rw [ih, mul_smul_comm, neg_smul]

private theorem evenCliffordAdjoin_le_subspace' {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a)) :
    (evenCliffordAdjoin γ).toSubmodule ≤ evenCliffordSubspace γ := by
  have hone_mem : (1 : A) ∈ evenCliffordSubspace γ :=
    Submodule.subset_span ⟨fun _ => false, by simp, by simp [cliffordMonomial, cliffordListProd]⟩
  have hnot_even_upd (f : Fin m → Bool) (c : Fin m) :
      Even (Finset.univ.filter fun a => Function.update f c (!f c) a = true).card ↔
        ¬ Even (Finset.univ.filter fun a => f a = true).card := by
    let S := Finset.univ.filter fun a => f a = true
    let S' := Finset.univ.filter fun a => Function.update f c (!f c) a = true
    change Even S'.card ↔ ¬ Even S.card
    cases hfc : f c
    · have hc_not : c ∉ S := by simp [S, hfc]
      have hS' : S' = insert c S := by
        ext a; by_cases hac : a = c <;> [subst hac; skip] <;> simp [S', S, *]
      rw [hS', Finset.card_insert_of_notMem hc_not, Nat.even_add_one]
    · have hc_not' : c ∉ S' := by simp [S', hfc]
      have hS : S = insert c S' := by
        ext a; by_cases hac : a = c <;> [subst hac; skip] <;> simp [S, S', *]
      rw [show S.card = S'.card + 1 by rw [hS, Finset.card_insert_of_notMem hc_not'],
        Nat.even_add_one, not_not]
  have hmul_two (a b : Fin m) : ∀ y ∈ evenCliffordSubspace γ,
      (γ a * γ b) * y ∈ evenCliffordSubspace γ := by
    intro y hy
    refine Submodule.span_induction ?_ (by simp)
      (fun u v _ _ hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      (fun r u _ hu => by rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu) hy
    rintro _ ⟨f, heven, rfl⟩
    obtain ⟨ε₁, _, h₁⟩ := mul_cliffordListProd_toggle' hsq hanti b (List.finRange m)
      (List.nodup_finRange m) (List.mem_finRange b) f
    let f₁ := Function.update f b (!f b)
    obtain ⟨ε₂, _, h₂⟩ := mul_cliffordListProd_toggle' hsq hanti a (List.finRange m)
      (List.nodup_finRange m) (List.mem_finRange a) f₁
    let f₂ := Function.update f₁ a (!f₁ a)
    have heven₂ : Even (Finset.univ.filter fun x => f₂ x = true).card := by
      dsimp [f₂, f₁]; rwa [hnot_even_upd, hnot_even_upd, not_not]
    have hprod_eq : (γ a * γ b) * cliffordMonomial γ f = (ε₁ * ε₂) • cliffordMonomial γ f₂ := by
      calc (γ a * γ b) * cliffordMonomial γ f
          = γ a * (γ b * cliffordListProd γ (List.finRange m) f) := mul_assoc _ _ _
        _ = (ε₁ * ε₂) • cliffordMonomial γ f₂ := by rw [h₁, mul_smul_comm, h₂, smul_smul]; rfl
    rw [hprod_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₂, heven₂, rfl⟩)
  intro w hw
  have hact : ∀ y ∈ evenCliffordSubspace γ, w * y ∈ evenCliffordSubspace γ := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hw
    · rintro x ⟨a, b, _, rfl⟩ y hy; exact hmul_two a b y hy
    · intro r y hy; rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact Submodule.smul_mem _ r hy
    · intro x₁ x₂ _ _ hx₁ hx₂ y hy; rw [add_mul]; exact Submodule.add_mem _ (hx₁ y hy) (hx₂ y hy)
    · intro x₁ x₂ _ _ hx₁ hx₂ y hy; rw [mul_assoc]; exact hx₁ _ (hx₂ y hy)
  simpa only [mul_one] using hact 1 hone_mem

private theorem isClosed_evenCliffordAdjoin' {A : Type*} [CStarAlgebra A] {m : ℕ}
    {γ : Fin m → A} (hsq : ∀ a, γ a * γ a = 1)
    (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a)) :
    IsClosed (evenCliffordAdjoin γ : Set A) := by
  have hfin_set : {M : A | ∃ f : Fin m → Bool,
      Even (Finset.univ.filter fun a => f a = true).card ∧ M = cliffordMonomial γ f}.Finite := by
    refine ((Set.finite_univ : (Set.univ : Set (Fin m → Bool)).Finite).image
      (cliffordMonomial γ)).subset ?_
    rintro _ ⟨f, _, rfl⟩; exact ⟨f, Set.mem_univ f, rfl⟩
  haveI : FiniteDimensional ℂ (evenCliffordSubspace γ) := FiniteDimensional.span_of_finite ℂ hfin_set
  haveI : FiniteDimensional ℂ (evenCliffordAdjoin γ).toSubmodule :=
    Submodule.finiteDimensional_of_le (evenCliffordAdjoin_le_subspace' hsq hanti)
  exact (evenCliffordAdjoin γ).toSubmodule.closed_of_finiteDimensional

end AbstractCliffordHelpers

/-- Full `2N`-mode Jordan-Wigner Pauli word on `n + 2` qubits (`2 * (n + 2)` Majorana modes):
`Γ_{2v} = Z_0 ⋯ Z_{v-1} X_v` and `Γ_{2v+1} = Z_0 ⋯ Z_{v-1} Y_v`. -/
def fullJWMajoranaWord (n : ℕ) (a : Fin (2 * (n + 2))) (s : Fin (n + 2)) : Option (Fin 3) :=
  if s.val < a.val / 2 then some 2
  else if s.val = a.val / 2 then (if a.val % 2 = 0 then some 0 else some 1)
  else none

/-- Full `2N`-mode Jordan-Wigner Majorana operator `Γ_a : Register (n + 2)`. -/
def fullJWMajorana (n : ℕ) (a : Fin (2 * (n + 2))) : Register (n + 2) :=
  finitePauliMatrix (fullJWMajoranaWord n a)

private theorem fullJWMajoranaWord_injective (n : ℕ) :
    Function.Injective (fullJWMajoranaWord n) := by
  intro a b hab
  by_contra hne
  have hlt_imp : ∀ {x y : Fin (2 * (n + 2))}, x < y → fullJWMajoranaWord n x ≠ fullJWMajoranaWord n y := by
    intro x y hxy heq
    let s₀ : Fin (n + 2) := ⟨x.val / 2, by omega⟩
    have h := congrFun heq s₀
    have hxv : x.val < y.val := hxy
    by_cases hdiv : x.val / 2 = y.val / 2
    · have hx0 : x.val % 2 = 0 := by omega
      have hy1 : y.val % 2 = 1 := by omega
      simp [fullJWMajoranaWord, s₀, hdiv, hx0, hy1] at h
    · have hlt_div : x.val / 2 < y.val / 2 := by omega
      simp only [fullJWMajoranaWord, s₀, lt_irrefl, hlt_div, ↓reduceIte] at h
      split_ifs at h <;> simp at h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt_imp hlt hab
  · exact hlt_imp hgt hab.symm

theorem fullJWMajorana_sq (n : ℕ) (a : Fin (2 * (n + 2))) :
    fullJWMajorana n a * fullJWMajorana n a = 1 :=
  finitePauliMatrix_mul_self _

theorem fullJWMajorana_star (n : ℕ) (a : Fin (2 * (n + 2))) :
    star (fullJWMajorana n a) = fullJWMajorana n a :=
  finitePauliMatrix_isHermitian _

theorem fullJWMajorana_anticommute (n : ℕ) {a b : Fin (2 * (n + 2))} (hab : a ≠ b) :
    fullJWMajorana n a * fullJWMajorana n b = -(fullJWMajorana n b * fullJWMajorana n a) := by
  have hlt_anti : ∀ {x y : Fin (2 * (n + 2))}, x < y →
      fullJWMajorana n x * fullJWMajorana n y = -(fullJWMajorana n y * fullJWMajorana n x) := by
    intro x y hxy
    unfold fullJWMajorana
    rw [finitePauliMatrix_mul, finitePauliMatrix_mul]
    have hlbl : (fun s => optMul (fullJWMajoranaWord n x s) (fullJWMajoranaWord n y s)) =
        fun s => optMul (fullJWMajoranaWord n y s) (fullJWMajoranaWord n x s) :=
      funext fun s => optMul_comm _ _
    let v₀ : Fin (n + 2) := ⟨x.val / 2, by omega⟩
    have hx_lt_y : x.val < y.val := hxy
    have hout1 : ∀ s ∈ ({v₀} : Finset (Fin (n + 2)))ᶜ,
        optPhase (fullJWMajoranaWord n x s) (fullJWMajoranaWord n y s) = 1 := by
      intro s hs
      have hsv : s.val ≠ x.val / 2 :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hsv with hslt | hsgt
      · have hsy : s.val < y.val / 2 := by omega
        simp [fullJWMajoranaWord, hslt, hsy, optPhase]
      · have hn1 : ¬ s.val < x.val / 2 := by omega
        simp [fullJWMajoranaWord, hn1, hsv, optPhase]
    have hout2 : ∀ s ∈ ({v₀} : Finset (Fin (n + 2)))ᶜ,
        optPhase (fullJWMajoranaWord n y s) (fullJWMajoranaWord n x s) = 1 := by
      intro s hs
      have hsv : s.val ≠ x.val / 2 :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hsv with hslt | hsgt
      · have hsy : s.val < y.val / 2 := by omega
        simp [fullJWMajoranaWord, hslt, hsy, optPhase]
      · have hn1 : ¬ s.val < x.val / 2 := by omega
        simp [fullJWMajoranaWord, hn1, hsv, optPhase_none_right]
    have hph : (∏ s : Fin (n + 2), optPhase (fullJWMajoranaWord n x s) (fullJWMajoranaWord n y s)) =
        -(∏ s : Fin (n + 2), optPhase (fullJWMajoranaWord n y s) (fullJWMajoranaWord n x s)) := by
      rw [← Finset.prod_mul_prod_compl ({v₀} : Finset (Fin (n + 2))),
        ← Finset.prod_mul_prod_compl ({v₀} : Finset (Fin (n + 2))),
        Finset.prod_singleton, Finset.prod_singleton,
        Finset.prod_eq_one hout1, Finset.prod_eq_one hout2, mul_one, mul_one]
      by_cases hdiv : x.val / 2 = y.val / 2
      · have hx0 : x.val % 2 = 0 := by omega
        have hy1 : y.val % 2 = 1 := by omega
        simp [fullJWMajoranaWord, v₀, hdiv, hx0, hy1, optPhase]
      · have hlt_div : x.val / 2 < y.val / 2 := by omega
        by_cases hmod : x.val % 2 = 0 <;>
          simp [fullJWMajoranaWord, v₀, hlt_div, hmod, optPhase]
    rw [hlbl, hph, neg_smul]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact hlt_anti hlt
  · rw [hlt_anti hgt, neg_neg]

/-- Weight-`≤ 2` Pauli word corresponding to the adjacent Majorana pair `Γ_r Γ_{r+1}` (`r + 1 < 2N`):
onsite `Z_{r/2}` for even `r`, and nearest-neighbor `X_{r/2} X_{r/2 + 1}` for odd `r`. -/
private def fullJWAdjWord (n : ℕ) (r : ℕ) (hr : r + 1 < 2 * (n + 2)) :
    Fin (n + 2) → Option (Fin 3) :=
  if h : r % 2 = 0 then onsiteWord ⟨r / 2, by omega⟩ 2
  else couplingWord ⟨r / 2, by omega⟩ (0, 0)

private theorem fullJWAdj_skew_eq_pair (n : ℕ) (r : ℕ) (hr : r + 1 < 2 * (n + 2)) :
    (-Complex.I) • finitePauliMatrix (fullJWAdjWord n r hr) =
      (-1 : ℂ) • (fullJWMajorana n ⟨r, by omega⟩ * fullJWMajorana n ⟨r + 1, hr⟩) := by
  unfold fullJWMajorana
  rw [finitePauliMatrix_mul]
  by_cases hmod : r % 2 = 0
  · let v : Fin (n + 2) := ⟨r / 2, by omega⟩
    have hr_div : (r + 1) / 2 = r / 2 := by omega
    have hr1_mod : (r + 1) % 2 = 1 := by omega
    have hadj_eq : fullJWAdjWord n r hr = onsiteWord v 2 := by
      unfold fullJWAdjWord; rw [dif_pos hmod]
    have hlbl : (fun s : Fin (n + 2) =>
        optMul (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s)) =
        fullJWAdjWord n r hr := by
      rw [hadj_eq]
      funext s
      by_cases hsv : s = v
      · subst hsv
        simp [fullJWMajoranaWord, v, hr_div, hmod, hr1_mod, onsiteWord, optMul]
      · have hval : s.val ≠ r / 2 := fun h => hsv (Fin.ext h)
        rcases lt_or_gt_of_ne hval with hslt | hsgt
        · simp [fullJWMajoranaWord, hr_div, hslt, onsiteWord, hsv, optMul]
        · have hn1 : ¬ s.val < r / 2 := by omega
          simp [fullJWMajoranaWord, hr_div, hn1, hval, onsiteWord, hsv, optMul]
    have hout : ∀ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ,
        optPhase (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s) = 1 := by
      intro s hs
      have hval : s.val ≠ r / 2 :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hval with hslt | hsgt
      · simp [fullJWMajoranaWord, hr_div, hslt, optPhase]
      · have hn1 : ¬ s.val < r / 2 := by omega
        simp [fullJWMajoranaWord, hr_div, hn1, hval, optPhase]
    have hph : (∏ s : Fin (n + 2),
        optPhase (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s)) =
        Complex.I := by
      rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))),
        Finset.prod_singleton, Finset.prod_eq_one hout, mul_one]
      simp [fullJWMajoranaWord, v, hr_div, hmod, hr1_mod, optPhase]
    rw [hlbl, hph, smul_smul]; norm_num
  · have hmod1 : r % 2 = 1 := by omega
    let e : Fin (n + 1) := ⟨r / 2, by omega⟩
    have hr_div1 : (r + 1) / 2 = e.val + 1 := by dsimp [e]; omega
    have hr1_mod : (r + 1) % 2 = 0 := by omega
    have hadj_eq : fullJWAdjWord n r hr = couplingWord e (0, 0) := by
      unfold fullJWAdjWord; rw [dif_neg hmod]
    have hlbl : (fun s : Fin (n + 2) =>
        optMul (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s)) =
        fullJWAdjWord n r hr := by
      rw [hadj_eq]
      funext s
      by_cases hs1 : s = e.castSucc
      · subst hs1
        have hlt1 : e.val < e.val + 1 := Nat.lt_succ_self e.val
        simp [fullJWMajoranaWord, e, hr_div1, hmod, hlt1, couplingWord, optMul]
      · by_cases hs2 : s = e.succ
        · subst hs2
          have hn1 : ¬ e.val + 1 < e.val := by omega
          simp [fullJWMajoranaWord, e, hr_div1, hr1_mod, hn1, couplingWord, optMul]
        · have hv1 : s.val ≠ e.val := fun h => hs1 (Fin.ext h)
          have hv2 : s.val ≠ e.val + 1 := fun h => hs2 (Fin.ext h)
          rw [couplingWord, if_neg hs1, if_neg hs2]
          rcases lt_or_gt_of_ne hv1 with hslt | hsgt
          · have hslt2 : s.val < e.val + 1 := by omega
            simp [fullJWMajoranaWord, e, hr_div1, hslt, hslt2, optMul]
          · have hn1 : ¬ s.val < e.val := by omega
            have hn2 : ¬ s.val < e.val + 1 := by omega
            simp [fullJWMajoranaWord, e, hr_div1, hn1, hn2, hv1, hv2, optMul]
    have hout : ∀ s ∈ ({e.castSucc} : Finset (Fin (n + 2)))ᶜ,
        optPhase (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s) = 1 := by
      intro s hs
      have hv1 : s.val ≠ e.val :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hv1 with hslt | hsgt
      · have hslt2 : s.val < e.val + 1 := by omega
        simp [fullJWMajoranaWord, e, hr_div1, hslt, hslt2, optPhase]
      · have hn1 : ¬ s.val < e.val := by omega
        simp [fullJWMajoranaWord, e, hr_div1, hn1, hv1, optPhase]
    have hph : (∏ s : Fin (n + 2),
        optPhase (fullJWMajoranaWord n ⟨r, by omega⟩ s) (fullJWMajoranaWord n ⟨r + 1, hr⟩ s)) =
        Complex.I := by
      rw [← Finset.prod_mul_prod_compl ({e.castSucc} : Finset (Fin (n + 2))),
        Finset.prod_singleton, Finset.prod_eq_one hout, mul_one]
      have hlt1 : e.val < e.val + 1 := Nat.lt_succ_self e.val
      simp [fullJWMajoranaWord, e, hr_div1, hmod, hlt1, optPhase]
    rw [hlbl, hph, smul_smul]; norm_num

private theorem matchgateLabel_skew_eq_pair {n : ℕ} (l : PathLabel n)
    (hl : isMatchgateChainLabel l) :
    ∃ (a b : Fin (2 * (n + 2))) (ε : ℝ),
      a ≠ b ∧ (ε = 1 ∨ ε = -1) ∧
      (-Complex.I) • finitePauliMatrix (pathWord l) =
        ((ε : ℝ) : ℂ) • (fullJWMajorana n a * fullJWMajorana n b) := by
  rcases l with ⟨v, c⟩ | ⟨e, ⟨p, q⟩⟩
  · dsimp [isMatchgateChainLabel] at hl
    subst hl
    have hr : 2 * v.val + 1 < 2 * (n + 2) := by omega
    have hadj := fullJWAdj_skew_eq_pair n (2 * v.val) hr
    have hmod0 : (2 * v.val) % 2 = 0 := by omega
    have hdiv : (2 * v.val) / 2 = v.val := by omega
    have hword : fullJWAdjWord n (2 * v.val) hr = pathWord (.inl (v, 2)) := by
      unfold fullJWAdjWord
      rw [dif_pos hmod0]
      have hv_eq : (⟨(2 * v.val) / 2, by omega⟩ : Fin (n + 2)) = v := Fin.ext hdiv
      rw [hv_eq]; rfl
    refine ⟨⟨2 * v.val, by omega⟩, ⟨2 * v.val + 1, hr⟩, -1,
      fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega, Or.inr rfl, ?_⟩
    rw [← hword, hadj]; norm_num
  · obtain ⟨hp2, hq2⟩ := hl
    have hp_01 : p = 0 ∨ p = 1 := by clear * - hp2; revert p hp2; decide
    have hq_01 : q = 0 ∨ q = 1 := by clear * - hq2; revert q hq2; decide
    let a : Fin (2 * (n + 2)) := ⟨2 * e.val + (if p = 0 then 1 else 0), by split_ifs <;> omega⟩
    let b : Fin (2 * (n + 2)) := ⟨2 * (e.val + 1) + (if q = 0 then 0 else 1), by split_ifs <;> omega⟩
    have hab : a ≠ b := fun h => by
      have hv := congrArg Fin.val h; dsimp [a, b] at hv; split_ifs at hv <;> omega
    have hadiv : a.val / 2 = e.val := by dsimp [a]; split_ifs <;> omega
    have hbdiv : b.val / 2 = e.val + 1 := by dsimp [b]; split_ifs <;> omega
    have hamod : (a.val % 2 = 0) ↔ p ≠ 0 := by dsimp [a]; split_ifs with hp0 <;> simp [hp0]
    have hbmod : (b.val % 2 = 0) ↔ q = 0 := by dsimp [b]; split_ifs with hq0 <;> simp [hq0]
    refine ⟨a, b, if p = 0 then -1 else 1, hab,
      by split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl], ?_⟩
    unfold fullJWMajorana
    rw [finitePauliMatrix_mul]
    have hlbl : (fun s : Fin (n + 2) =>
        optMul (fullJWMajoranaWord n a s) (fullJWMajoranaWord n b s)) =
        pathWord (.inr (e, (p, q))) := by
      funext s
      by_cases hs1 : s = e.castSucc
      · subst hs1
        have hlt1 : e.val < e.val + 1 := Nat.lt_succ_self e.val
        simp only [fullJWMajoranaWord, hadiv, hbdiv, Fin.val_castSucc, lt_irrefl, hlt1, ↓reduceIte,
          pathWord, couplingWord]
        rcases hp_01 with rfl | rfl <;> simp [hamod, optMul]
      · by_cases hs2 : s = e.succ
        · subst hs2
          have hn1 : ¬ e.val + 1 < e.val := by omega
          have hne1 : e.val + 1 ≠ e.val := by omega
          simp only [fullJWMajoranaWord, hadiv, hbdiv, Fin.val_succ, hn1, hne1, lt_irrefl, ↓reduceIte,
            pathWord, couplingWord, e.castSucc_lt_succ.ne']
          rcases hq_01 with rfl | rfl <;> simp [hbmod, optMul]
        · have hv1 : s.val ≠ e.val := fun h => hs1 (Fin.ext h)
          have hv2 : s.val ≠ e.val + 1 := fun h => hs2 (Fin.ext h)
          rcases lt_or_gt_of_ne hv1 with hslt | hsgt
          · have hslt2 : s.val < e.val + 1 := by omega
            simp [fullJWMajoranaWord, hadiv, hbdiv, hslt, hslt2, pathWord, couplingWord, hs1, hs2, optMul]
          · have hn1 : ¬ s.val < e.val := by omega
            have hn2 : ¬ s.val < e.val + 1 := by omega
            simp [fullJWMajoranaWord, hadiv, hbdiv, hn1, hn2, hv1, hv2, pathWord, couplingWord, hs1, hs2, optMul]
    have hout : ∀ s ∈ ({e.castSucc} : Finset (Fin (n + 2)))ᶜ,
        optPhase (fullJWMajoranaWord n a s) (fullJWMajoranaWord n b s) = 1 := by
      intro s hs
      have hv1 : s.val ≠ e.val :=
        fun h => (Finset.mem_compl.mp hs) (Finset.mem_singleton.mpr (Fin.ext h))
      rcases lt_or_gt_of_ne hv1 with hslt | hsgt
      · have hslt2 : s.val < e.val + 1 := by omega
        simp [fullJWMajoranaWord, hadiv, hbdiv, hslt, hslt2, optPhase]
      · have hn1 : ¬ s.val < e.val := by omega
        simp [fullJWMajoranaWord, hadiv, hbdiv, hn1, hv1, optPhase]
    have hph : (∏ s : Fin (n + 2),
        optPhase (fullJWMajoranaWord n a s) (fullJWMajoranaWord n b s)) =
        if p = 0 then Complex.I else -Complex.I := by
      rw [← Finset.prod_mul_prod_compl ({e.castSucc} : Finset (Fin (n + 2))),
        Finset.prod_singleton, Finset.prod_eq_one hout, mul_one]
      have hlt1 : e.val < e.val + 1 := Nat.lt_succ_self e.val
      simp only [fullJWMajoranaWord, hadiv, hbdiv, Fin.val_castSucc, lt_irrefl, hlt1, ↓reduceIte]
      rcases hp_01 with rfl | rfl <;> simp [hamod, optPhase]
    rw [hlbl, hph, smul_smul]
    congr 1
    rcases hp_01 with rfl | rfl <;> simp

/-- Real `2N`-Majorana subspace `span_ℝ {Γ_0, …, Γ_{2N - 1}} ⊆ Register (n + 2)`. -/
def fullRealMajoranaSubspace (n : ℕ) : Submodule ℝ (Register (n + 2)) :=
  Submodule.span ℝ (Set.range (fullJWMajorana n))

private def fullMajCoeff (n : ℕ) (M : Register (n + 2)) (a : Fin (2 * (n + 2))) : ℝ :=
  (Matrix.trace (fullJWMajorana n a * M)).re / (2 ^ (n + 2) : ℝ)

private def fullMajMat (n : ℕ) (U : Register (n + 2)) :
    Matrix (Fin (2 * (n + 2))) (Fin (2 * (n + 2))) ℝ :=
  fun a c => fullMajCoeff n (U * fullJWMajorana n c * star U) a

private theorem fullMajCoeff_majorana (n : ℕ) (a b : Fin (2 * (n + 2))) :
    fullMajCoeff n (fullJWMajorana n b) a = if a = b then 1 else 0 := by
  unfold fullMajCoeff fullJWMajorana
  rw [trace_pauli_mul, Fintype.card_fin]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl,
      show ((2 : ℂ) ^ (n + 2)).re = (2 : ℝ) ^ (n + 2) by
        rw [show ((2 : ℂ) ^ (n + 2)) = (((2 : ℝ) ^ (n + 2) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_re]]
    exact div_self (pow_ne_zero _ two_ne_zero)
  · rw [if_neg (fun h => hab (fullJWMajoranaWord_injective n h)), if_neg hab, Complex.zero_re, zero_div]

private theorem fullMajCoeff_add (n : ℕ) (M₁ M₂ : Register (n + 2)) (a : Fin (2 * (n + 2))) :
    fullMajCoeff n (M₁ + M₂) a = fullMajCoeff n M₁ a + fullMajCoeff n M₂ a := by
  unfold fullMajCoeff
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, add_div]

private theorem fullMajCoeff_real_smul (n : ℕ) (r : ℝ) (M : Register (n + 2))
    (a : Fin (2 * (n + 2))) :
    fullMajCoeff n (r • M) a = r * fullMajCoeff n M a := by
  unfold fullMajCoeff
  have h1 : fullJWMajorana n a * (r • M) = (r : ℂ) • (fullJWMajorana n a * M) := by
    rw [← Complex.coe_smul, Matrix.mul_smul]
  rw [h1, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_div_assoc]

private theorem eq_sum_fullMajCoeff {n : ℕ} {M : Register (n + 2)}
    (hM : M ∈ fullRealMajoranaSubspace n) :
    M = ∑ a : Fin (2 * (n + 2)), ((fullMajCoeff n M a : ℝ) : ℂ) • fullJWMajorana n a := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hM
  · rintro _ ⟨b, rfl⟩
    simp_rw [fullMajCoeff_majorana]
    rw [Finset.sum_eq_single b (fun a _ hab => by simp [hab]) (by simp)]
    simp
  · unfold fullMajCoeff; simp [Matrix.trace_zero, zero_div]
  · intro x y _ _ hx hy
    simp_rw [fullMajCoeff_add, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  · intro r x _ hx
    simp_rw [fullMajCoeff_real_smul, Complex.ofReal_mul, ← smul_smul, ← Finset.smul_sum, ← Complex.coe_smul]
    rw [Complex.coe_smul, ← hx]
    exact (Complex.coe_smul r x).symm

private theorem fullMajMat_one (n : ℕ) : fullMajMat n 1 = 1 := by
  ext a c; simp [fullMajMat, fullMajCoeff_majorana, Matrix.one_apply]

private theorem fullMajMat_mul {n : ℕ} {U₁ U₂ : Register (n + 2)}
    (hU₂ : ∀ c, U₂ * fullJWMajorana n c * star U₂ ∈ fullRealMajoranaSubspace n) :
    fullMajMat n (U₁ * U₂) = fullMajMat n U₁ * fullMajMat n U₂ := by
  ext a c
  rw [Matrix.mul_apply]
  have hexp := eq_sum_fullMajCoeff (hU₂ c)
  have hconj : (U₁ * U₂) * fullJWMajorana n c * star (U₁ * U₂) =
      ∑ b : Fin (2 * (n + 2)), (fullMajMat n U₂ b c) • (U₁ * fullJWMajorana n b * star U₁) := by
    calc (U₁ * U₂) * fullJWMajorana n c * star (U₁ * U₂)
        = U₁ * (U₂ * fullJWMajorana n c * star U₂) * star U₁ := by rw [star_mul]; simp only [mul_assoc]
      _ = U₁ * (∑ b, ((fullMajMat n U₂ b c : ℝ) : ℂ) • fullJWMajorana n b) * star U₁ := by rw [hexp]; rfl
      _ = _ := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
  dsimp only [fullMajMat]
  rw [hconj]
  have hsum_lin : ∀ (S : Finset (Fin (2 * (n + 2)))) (f : Fin (2 * (n + 2)) → ℝ)
      (g : Fin (2 * (n + 2)) → Register (n + 2)),
      fullMajCoeff n (∑ b ∈ S, f b • g b) a = ∑ b ∈ S, f b * fullMajCoeff n (g b) a := by
    intro S f g
    induction S using Finset.induction_on with
    | empty => simp [fullMajCoeff]
    | @insert b S hb ih =>
        rw [Finset.sum_insert hb, fullMajCoeff_add, fullMajCoeff_real_smul, ih, Finset.sum_insert hb]
  rw [hsum_lin]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private theorem fullMajMat_star_eq_transpose {n : ℕ} (U : Register (n + 2)) :
    fullMajMat n (star U) = (fullMajMat n U)ᵀ := by
  ext a c
  simp only [fullMajMat, Matrix.transpose_apply, fullMajCoeff, star_star]
  refine congrArg (· / (2 ^ (n + 2) : ℝ)) ?_
  have htr_star (X : Register (n + 2)) : star (Matrix.trace X) = Matrix.trace (star X) := by
    simp [Matrix.trace, star_sum]
  have hst_tr : star (Matrix.trace (fullJWMajorana n a * (star U * fullJWMajorana n c * U))) =
      Matrix.trace (fullJWMajorana n c * (U * fullJWMajorana n a * star U)) := by
    rw [htr_star, star_mul, star_mul, star_mul, star_star, fullJWMajorana_star, fullJWMajorana_star]
    calc Matrix.trace ((star U * (fullJWMajorana n c * U)) * fullJWMajorana n a)
        = Matrix.trace (star U * (fullJWMajorana n c * (U * fullJWMajorana n a))) := by simp only [mul_assoc]
      _ = Matrix.trace ((fullJWMajorana n c * (U * fullJWMajorana n a)) * star U) :=
            Matrix.trace_mul_comm (star U) _
      _ = Matrix.trace (fullJWMajorana n c * (U * fullJWMajorana n a * star U)) := by simp only [mul_assoc]
  have hre := congrArg Complex.re hst_tr
  simpa only [Complex.star_def, Complex.conj_re] using hre

private theorem fullJWAdjGate_preserves_and_majMat (n : ℕ) (r : ℕ) (hr : r + 1 < 2 * (n + 2))
    (φ : ℝ) :
    let U := unitaryEvolution (finitePauliMatrix (fullJWAdjWord n r hr)) (-(φ / 2))
    U ∈ unitary (Register (n + 2)) ∧
    star U ∈ evenCliffordAdjoin (fullJWMajorana n) ∧
    (∀ c, U * fullJWMajorana n c * star U ∈ fullRealMajoranaSubspace n) ∧
    fullMajMat n U = adjGivens (2 * (n + 2)) r φ ∧
    Realizes 1 U := by
  intro U
  let _ : NormedAlgebra ℚ (Register (n + 2)) := .restrictScalars ℚ ℂ (Register (n + 2))
  let a₀ : Fin (2 * (n + 2)) := ⟨r, by omega⟩
  let a₁ : Fin (2 * (n + 2)) := ⟨r + 1, hr⟩
  have hne01 : a₀ ≠ a₁ := fun h => by have hv := congrArg Fin.val h; dsimp [a₀, a₁] at hv; omega
  have hU_exp_eq : U = NormedSpace.exp (((φ / 2 : ℝ) : ℂ) •
      (fullJWMajorana n a₀ * fullJWMajorana n a₁)) := by
    dsimp only [U, unitaryEvolution, a₀, a₁]
    rw [fullJWAdj_skew_eq_pair n r hr, ← Complex.coe_smul, smul_smul]
    congr 1; push_cast; ring
  have hgen_adjoin : fullJWMajorana n a₀ * fullJWMajorana n a₁ ∈
      evenCliffordAdjoin (fullJWMajorana n) :=
    Algebra.subset_adjoin ⟨a₀, a₁, hne01, rfl⟩
  have hclosed := isClosed_evenCliffordAdjoin' (fullJWMajorana_sq n)
    (fun _ _ h => fullJWMajorana_anticommute n h)
  have hstU_adj : star U ∈ evenCliffordAdjoin (fullJWMajorana n) := by
    rw [hU_exp_eq, exp_skewPair_star_eq' (fullJWMajorana_star n _) (fullJWMajorana_star n _)
      (fullJWMajorana_anticommute n hne01)]
    exact NormedSpace.exp_mem (R := ℂ) hclosed (Subalgebra.smul_mem _ hgen_adjoin _)
  have hU_unit : U ∈ unitary (Register (n + 2)) :=
    unitaryEvolution_mem_unitary (finitePauliMatrix_isHermitian _) (-(φ / 2))
  obtain ⟨hc1, hc2, hco⟩ := exp_skewPair_conj' (fullJWMajorana_sq n a₀) (fullJWMajorana_sq n a₁)
    (fullJWMajorana_star n a₀) (fullJWMajorana_star n a₁)
    (fullJWMajorana_anticommute n hne01) φ
  rw [← hU_exp_eq] at hc1 hc2 hco
  have hpres (c : Fin (2 * (n + 2))) :
      U * fullJWMajorana n c * star U ∈ fullRealMajoranaSubspace n := by
    by_cases h1 : c = a₀
    · subst h1; rw [hc1, Complex.coe_smul, Complex.coe_smul]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · by_cases h2 : c = a₁
      · subst h2; rw [hc2, Complex.coe_smul, Complex.coe_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      · rw [hco (fullJWMajorana n c) (fullJWMajorana_anticommute n (Ne.symm h1))
          (fullJWMajorana_anticommute n (Ne.symm h2))]
        exact Submodule.subset_span ⟨c, rfl⟩
  have hmaj : fullMajMat n U = adjGivens (2 * (n + 2)) r φ := by
    ext a c
    dsimp only [fullMajMat]
    by_cases h1 : c = a₀
    · subst h1
      rw [hc1, Complex.coe_smul, Complex.coe_smul, fullMajCoeff_add, fullMajCoeff_real_smul,
        fullMajCoeff_real_smul, fullMajCoeff_majorana, fullMajCoeff_majorana]
      by_cases ha1 : a = a₀
      · subst ha1; simp [adjGivens, a₀, a₁, hne01]
      · by_cases ha2 : a = a₁
        · subst ha2; simp [adjGivens, a₀, a₁, hne01.symm]
        · have hv1 : a.val ≠ r := fun h => ha1 (Fin.ext h)
          have hv2 : a.val ≠ r + 1 := fun h => ha2 (Fin.ext h)
          simp [adjGivens, a₀, a₁, ha1, ha2, hv1, hv2]
    · by_cases h2 : c = a₁
      · subst h2
        rw [hc2, Complex.coe_smul, Complex.coe_smul, fullMajCoeff_add, fullMajCoeff_real_smul,
          fullMajCoeff_real_smul, fullMajCoeff_majorana, fullMajCoeff_majorana]
        by_cases ha1 : a = a₀
        · subst ha1; simp [adjGivens, a₀, a₁, hne01]
        · by_cases ha2 : a = a₁
          · subst ha2; simp [adjGivens, a₀, a₁, hne01.symm]
          · have hv1 : a.val ≠ r := fun h => ha1 (Fin.ext h)
            have hv2 : a.val ≠ r + 1 := fun h => ha2 (Fin.ext h)
            simp [adjGivens, a₀, a₁, ha1, ha2, hv1, hv2]
      · rw [hco (fullJWMajorana n c) (fullJWMajorana_anticommute n (Ne.symm h1))
          (fullJWMajorana_anticommute n (Ne.symm h2)), fullMajCoeff_majorana]
        have hc1v : c.val ≠ r := fun h => h1 (Fin.ext h)
        have hc2v : c.val ≠ r + 1 := fun h => h2 (Fin.ext h)
        simp [adjGivens, hc1v, hc2v]
  have hreal1 : Realizes 1 U := by
    have hn2 : 2 ≤ n + 2 := by omega
    have hw_le2 : pauliWeight (fullJWAdjWord n r hr) ≤ 2 := by
      unfold pauliWeight fullJWAdjWord
      by_cases hmod : r % 2 = 0
      · rw [dif_pos hmod]
        let v : Fin (n + 2) := ⟨r / 2, by omega⟩
        have hsub : (Finset.univ.filter fun s => onsiteWord v 2 s ≠ none) ⊆ {v} := by
          intro s hs
          rw [Finset.mem_singleton]
          by_contra hv
          exact (Finset.mem_filter.mp hs).2 (by simp [onsiteWord, hv])
        exact (Finset.card_le_card hsub).trans (by simp)
      · rw [dif_neg hmod]
        let e : Fin (n + 1) := ⟨r / 2, by omega⟩
        have hsub : (Finset.univ.filter fun s => couplingWord e (0, 0) s ≠ none) ⊆
            {e.castSucc, e.succ} := by
          intro s hs
          have hne := (Finset.mem_filter.mp hs).2
          by_contra hout
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
          exact hne (by simp [couplingWord, hout.1, hout.2])
        exact (Finset.card_le_card hsub).trans (Finset.card_pair e.castSucc_lt_succ.ne).le
    have hnot_id : fullJWAdjWord n r hr ≠ pauliIdentityLabel (n + 2) := by
      intro hid
      by_cases hmod : r % 2 = 0
      · have h := congrFun hid ⟨r / 2, by omega⟩
        unfold fullJWAdjWord at h
        rw [dif_pos hmod] at h
        simp [onsiteWord, pauliIdentityLabel] at h
      · let e : Fin (n + 1) := ⟨r / 2, by omega⟩
        have h := congrFun hid e.castSucc
        unfold fullJWAdjWord at h
        rw [dif_neg hmod] at h
        simp [couplingWord, e, pauliIdentityLabel] at h
    let Q : PauliTracelessLabel (n + 2) 2 := ⟨fullJWAdjWord n r hr, hw_le2, hnot_id⟩
    let H_b := finitePauliSelfAdjointBasis (Fin (n + 2)) (fullJWAdjWord n r hr)
    have hc : realPauliCoefficient H_b Q.val = 1 := by
      change (finitePauliSelfAdjointBasis (Fin (n + 2))).repr
        ((finitePauliSelfAdjointBasis (Fin (n + 2))) (fullJWAdjWord n r hr))
        (fullJWAdjWord n r hr) = 1
      rw [Module.Basis.repr_self, Finsupp.single_eq_same]
    obtain ⟨z, hz, G, hG⟩ := exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator
      hn2 H_b Q (-(φ / 2))
    refine ⟨z, hz, TwoQubitCircuit.singleOn _ _ (Q.coveringPair_distinct hn2) G, le_rfl, ?_⟩
    rw [TwoQubitCircuit.singleOn_eval]
    simpa only [twoLocalSkewGenerator, hc, Complex.ofReal_one, one_smul, unitaryEvolution, U] using hG
  exact ⟨hU_unit, hstU_adj, hpres, hmaj, hreal1⟩

private theorem matchgateChain_evolution_mem_adjoin_and_preserves {n : ℕ} (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬ isMatchgateChainLabel l → u l = 0) (s : ℝ) :
    unitaryEvolution (pathHamiltonian u) s ∈ evenCliffordAdjoin (fullJWMajorana n) ∧
    ∀ c : Fin (2 * (n + 2)),
      unitaryEvolution (pathHamiltonian u) s * fullJWMajorana n c *
        star (unitaryEvolution (pathHamiltonian u) s) ∈ fullRealMajoranaSubspace n := by
  let _ : NormedAlgebra ℚ (Register (n + 2)) := .restrictScalars ℚ ℂ (Register (n + 2))
  let H := pathHamiltonian u
  have hH_sa : IsSelfAdjoint H := isSelfAdjoint_pathHamiltonian u
  let S_mg : Finset (PathLabel n) := Finset.univ.filter isMatchgateChainLabel
  have hH_eq : H = ∑ l ∈ S_mg, ((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) := by
    dsimp only [H]
    rw [pathHamiltonian_eq_sum, ← Finset.sum_subset S_mg.subset_univ]
    intro l _ hl
    have hnot : ¬ isMatchgateChainLabel l := fun h => hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
    rw [hu l hnot, Complex.ofReal_zero, zero_smul]
  have hclosed_adj := isClosed_evenCliffordAdjoin' (fullJWMajorana_sq n)
    (fun _ _ h => fullJWMajorana_anticommute n h)
  have hskew_adjoin : s • ((-Complex.I) • H) ∈ evenCliffordAdjoin (fullJWMajorana n) := by
    rw [hH_eq, Finset.smul_sum, Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun l hl => ?_
    obtain ⟨a, b, ε, hab, _, hpair⟩ := matchgateLabel_skew_eq_pair l (Finset.mem_filter.mp hl).2
    have h1 : s • ((-Complex.I) • (((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))) =
        ((s * u l * ε : ℝ) : ℂ) • (fullJWMajorana n a * fullJWMajorana n b) := by
      rw [smul_comm (-Complex.I), hpair, ← Complex.coe_smul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    rw [h1]
    have hab_mem : fullJWMajorana n a * fullJWMajorana n b ∈
        evenCliffordAdjoin (fullJWMajorana n) :=
      Algebra.subset_adjoin ⟨a, b, hab, rfl⟩
    exact Subalgebra.smul_mem _ hab_mem _
  have hUt_adjoin : unitaryEvolution H s ∈ evenCliffordAdjoin (fullJWMajorana n) :=
    NormedSpace.exp_mem (R := ℂ) hclosed_adj hskew_adjoin
  have had_mem : ∀ M ∈ fullRealMajoranaSubspace n,
      Complex.I • (H * M - M * H) ∈ fullRealMajoranaSubspace n := by
    intro M hM
    refine Submodule.span_induction ?_ (by simp)
      (fun x y _ _ hx hy => by
        rw [show H * (x + y) - (x + y) * H = (H * x - x * H) + (H * y - y * H) by
          rw [mul_add, add_mul]; abel, smul_add]
        exact Submodule.add_mem _ hx hy)
      (fun r x _ hx => by
        have h : Complex.I • (H * (r • x) - (r • x) * H) = r • (Complex.I • (H * x - x * H)) := by
          rw [← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_comm Complex.I,
            Complex.coe_smul]
        rw [h]; exact Submodule.smul_mem _ r hx) hM
    rintro _ ⟨c, rfl⟩
    rw [hH_eq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Submodule.sum_mem _ fun l hl => ?_
    obtain ⟨a, b, ε, hab, _, hpair⟩ := matchgateLabel_skew_eq_pair l (Finset.mem_filter.mp hl).2
    have hPl : Complex.I • finitePauliMatrix (pathWord l) =
        ((-ε : ℝ) : ℂ) • (fullJWMajorana n a * fullJWMajorana n b) := by
      have h := congrArg Neg.neg hpair
      simpa only [neg_smul, neg_neg, Complex.ofReal_neg] using h
    have hterm_eq : Complex.I • ((((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)) *
          fullJWMajorana n c -
        fullJWMajorana n c * (((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))) =
        ((-u l * ε : ℝ) : ℂ) •
          ((fullJWMajorana n a * fullJWMajorana n b) * fullJWMajorana n c -
            fullJWMajorana n c * (fullJWMajorana n a * fullJWMajorana n b)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_comm Complex.I, smul_sub,
        ← Matrix.smul_mul, ← Matrix.mul_smul, hPl, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_sub, smul_smul]
      congr 1; push_cast; ring
    rw [hterm_eq]
    by_cases h1 : c = a
    · subst h1
      have ha := fullJWMajorana_anticommute n hab
      have hL : (fullJWMajorana n c * fullJWMajorana n b) * fullJWMajorana n c = -fullJWMajorana n b := by
        rw [ha, neg_mul, mul_assoc, fullJWMajorana_sq, mul_one]
      have hR : fullJWMajorana n c * (fullJWMajorana n c * fullJWMajorana n b) = fullJWMajorana n b := by
        rw [← mul_assoc, fullJWMajorana_sq, one_mul]
      have hcomm1 : (fullJWMajorana n c * fullJWMajorana n b) * fullJWMajorana n c -
          fullJWMajorana n c * (fullJWMajorana n c * fullJWMajorana n b) =
          ((-2 : ℝ) : ℂ) • fullJWMajorana n b := by
        rw [hL, hR]
        calc -fullJWMajorana n b - fullJWMajorana n b
            = (-1 : ℂ) • fullJWMajorana n b + (-1 : ℂ) • fullJWMajorana n b := by simp [sub_eq_add_neg]
          _ = ((-2 : ℝ) : ℂ) • fullJWMajorana n b := by rw [← add_smul]; norm_num
      rw [hcomm1, smul_smul, ← Complex.ofReal_mul, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · by_cases h2 : c = b
      · subst h2
        have ha := fullJWMajorana_anticommute n hab.symm
        have hL : (fullJWMajorana n a * fullJWMajorana n c) * fullJWMajorana n c = fullJWMajorana n a := by
          rw [mul_assoc, fullJWMajorana_sq, mul_one]
        have hR : fullJWMajorana n c * (fullJWMajorana n a * fullJWMajorana n c) = -fullJWMajorana n a := by
          rw [← mul_assoc, ha, neg_mul, mul_assoc, fullJWMajorana_sq, mul_one]
        have hcomm2 : (fullJWMajorana n a * fullJWMajorana n c) * fullJWMajorana n c -
            fullJWMajorana n c * (fullJWMajorana n a * fullJWMajorana n c) =
            ((2 : ℝ) : ℂ) • fullJWMajorana n a := by
          rw [hL, hR, sub_neg_eq_add, ← two_smul ℂ]; norm_num
        rw [hcomm2, smul_smul, ← Complex.ofReal_mul, Complex.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · have ha1 := fullJWMajorana_anticommute n (Ne.symm h1)
        have ha2 := fullJWMajorana_anticommute n (Ne.symm h2)
        have hcomm0 : (fullJWMajorana n a * fullJWMajorana n b) * fullJWMajorana n c -
            fullJWMajorana n c * (fullJWMajorana n a * fullJWMajorana n b) = 0 := by
          rw [mul_assoc, ha2, mul_neg, ← mul_assoc, ha1, neg_mul, neg_neg, mul_assoc, sub_self]
        rw [hcomm0, smul_zero]; exact Submodule.zero_mem _
  have hiter_mem : ∀ k : ℕ, ∀ M ∈ fullRealMajoranaSubspace n,
      (Complex.I ^ k) • iteratedCommutator H k M ∈ fullRealMajoranaSubspace n := by
    intro k; induction k with
    | zero => intro M hM; simpa only [pow_zero, one_smul, iteratedCommutator] using hM
    | succ k ih =>
        intro M hM
        have hsmul_iter : ∀ (m : ℕ) (z : ℂ) (X : Register (n + 2)),
            z • iteratedCommutator H m X = iteratedCommutator H m (z • X) := by
          intro m z; induction m with
          | zero => intro _; rfl
          | succ m ihm => intro X; dsimp only [iteratedCommutator]; rw [ihm, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
        rw [show (Complex.I ^ (k + 1)) • iteratedCommutator H (k + 1) M =
          (Complex.I ^ k) • iteratedCommutator H k (Complex.I • (H * M - M * H)) by
            dsimp only [iteratedCommutator]; rw [pow_succ, mul_smul, hsmul_iter k Complex.I]]
        exact ih _ (had_mem M hM)
  have hclosed_real : IsClosed (fullRealMajoranaSubspace n : Set (Register (n + 2))) := by
    haveI : FiniteDimensional ℝ (fullRealMajoranaSubspace n) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    exact (fullRealMajoranaSubspace n).closed_of_finiteDimensional
  refine ⟨hUt_adjoin, fun c => ?_⟩
  have horb_eq : unitaryEvolution H s * fullJWMajorana n c * star (unitaryEvolution H s) =
      heisenbergOrbit H (fullJWMajorana n c) (-s) := by
    unfold heisenbergOrbit unitaryEvolution
    have hst (u_s : ℝ) : star (NormedSpace.exp (u_s • ((-Complex.I) • H))) =
        NormedSpace.exp ((-u_s) • ((-Complex.I) • H)) := by
      rw [NormedSpace.star_exp, star_smul, star_smul, hH_sa.star_eq]; simp [neg_smul, smul_neg]
    rw [hst s, hst (-s), neg_neg]
  rw [horb_eq]
  have htay_mem (K : ℕ) :
      heisenbergCommutatorTaylor H (fullJWMajorana n c) K (-s) ∈ fullRealMajoranaSubspace n := by
    unfold heisenbergCommutatorTaylor
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show ((((-s) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * Complex.I ^ k) •
        iteratedCommutator H k (fullJWMajorana n c) =
        ((-s) ^ k / (k.factorial : ℝ)) •
          ((Complex.I ^ k) • iteratedCommutator H k (fullJWMajorana n c)) by
      rw [← Complex.coe_smul, smul_smul]]
    exact Submodule.smul_mem _ _ (hiter_mem k _ (Submodule.subset_span ⟨c, rfl⟩))
  let R := 2 * ‖H‖ * |-s|
  have hsum_R : Summable (fun k : ℕ => R ^ k / (k.factorial : ℝ)) := by
    have hs := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) R).summable
    rwa [NormedSpace.expSeries_apply_eq_div' (𝕂 := ℝ) R] at hs
  have htend0 : Tendsto
      (fun K : ℕ => R ^ (K + 1) / ((K + 1).factorial : ℝ) * ‖fullJWMajorana n c‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (hsum_R.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)).mul_const ‖fullJWMajorana n c‖
  have htend_tay : Tendsto
      (fun K : ℕ => heisenbergCommutatorTaylor H (fullJWMajorana n c) K (-s)) atTop
      (𝓝 (heisenbergOrbit H (fullJWMajorana n c) (-s))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) htend0
    rw [norm_sub_rev]
    exact norm_heisenbergOrbit_sub_commutatorTaylor_le hH_sa (fullJWMajorana n c) K (-s)
  exact hclosed_real.mem_of_tendsto htend_tay (Eventually.of_forall htay_mem)

/-- Exact `choose(2N, 2) = (n + 2) * (2 * n + 3)`-gate `Spin(2N)` compilation of every
`(5N - 4)`-parameter `isMatchgateChainLabel` chain Hamiltonian on `n + 2` qubits for **all**
`t ∈ ℝ`. -/
theorem realizes_choose_twoN_of_matchgateChain {n : ℕ} (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬ isMatchgateChainLabel l → u l = 0) (t : ℝ) :
    Realizes ((n + 2) * (2 * n + 3)) (unitaryEvolution (pathHamiltonian u) t) := by
  let _ : NormedAlgebra ℚ (Register (n + 2)) := .restrictScalars ℚ ℂ (Register (n + 2))
  let H := pathHamiltonian u
  have hH_sa : IsSelfAdjoint H := isSelfAdjoint_pathHamiltonian u
  have hUt_adjoin (s : ℝ) : unitaryEvolution H s ∈ evenCliffordAdjoin (fullJWMajorana n) :=
    (matchgateChain_evolution_mem_adjoin_and_preserves u hu s).1
  have hUt_pres (s : ℝ) (c : Fin (2 * (n + 2))) :
      unitaryEvolution H s * fullJWMajorana n c * star (unitaryEvolution H s) ∈
        fullRealMajoranaSubspace n :=
    (matchgateChain_evolution_mem_adjoin_and_preserves u hu s).2 c
  let U_t := unitaryEvolution H t
  let O_t := fullMajMat n U_t
  have hUt_unit : ∀ s : ℝ, unitaryEvolution H s ∈ unitary (Register (n + 2)) :=
    fun s => unitaryEvolution_mem_unitary hH_sa s
  have hUt_inv (s : ℝ) : star (unitaryEvolution H s) = unitaryEvolution H (-s) := by
    unfold unitaryEvolution
    rw [NormedSpace.star_exp, star_smul, star_smul, hH_sa.star_eq]; simp [neg_smul, smul_neg]
  have hOt_orthL : O_tᵀ * O_t = 1 := by
    dsimp [O_t]
    rw [← fullMajMat_star_eq_transpose, ← fullMajMat_mul (hUt_pres t),
      (Unitary.mem_iff.mp (hUt_unit t)).1, fullMajMat_one]
  have hOt_orthR : O_t * O_tᵀ = 1 := by
    dsimp [O_t]
    rw [← fullMajMat_star_eq_transpose]
    have hpres_st : ∀ c, star U_t * fullJWMajorana n c * star (star U_t) ∈
        fullRealMajoranaSubspace n := by
      intro c; dsimp [U_t]; rw [hUt_inv t]; exact hUt_pres (-t) c
    rw [← fullMajMat_mul hpres_st, (Unitary.mem_iff.mp (hUt_unit t)).2, fullMajMat_one]
  have hOt_det : O_t.det = 1 := by
    have hhalf : U_t = unitaryEvolution H (t / 2) * unitaryEvolution H (t / 2) := by
      dsimp [U_t]; unfold unitaryEvolution
      rw [← NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _),
        ← add_smul, add_halves]
    have hOmul : O_t = fullMajMat n (unitaryEvolution H (t / 2)) *
        fullMajMat n (unitaryEvolution H (t / 2)) := by
      dsimp [O_t]; rw [hhalf, fullMajMat_mul (hUt_pres (t / 2))]
    have hdet_nn : 0 ≤ O_t.det := by rw [hOmul, Matrix.det_mul, ← sq]; exact sq_nonneg _
    have hdet_sq : O_t.det ^ 2 = 1 := by
      have hd := congrArg Matrix.det hOt_orthL
      rwa [Matrix.det_mul, Matrix.det_transpose, ← sq, Matrix.det_one] at hd
    nlinarith only [hdet_nn, hdet_sq, sq_nonneg (O_t.det - 1)]
  obtain ⟨L_giv, hlen_giv, hp_giv, hOt_prod⟩ :=
    exists_adjGivens_prod_eq_of_specialOrthogonal (2 * (n + 2)) O_t hOt_orthL hOt_orthR hOt_det
  have hcompile : ∀ (L : List (ℕ × ℝ)), (∀ p ∈ L, p.1 + 1 < 2 * (n + 2)) →
      ∃ U_c : Register (n + 2),
        U_c ∈ unitary (Register (n + 2)) ∧
        star U_c ∈ evenCliffordAdjoin (fullJWMajorana n) ∧
        (∀ c, U_c * fullJWMajorana n c * star U_c ∈ fullRealMajoranaSubspace n) ∧
        fullMajMat n U_c = (L.map fun p => adjGivens (2 * (n + 2)) p.1 p.2).prod ∧
        Realizes L.length U_c := by
    intro L; induction L with
    | nil =>
        intro _
        refine ⟨1, OneMemClass.one_mem _, by rw [star_one]; exact OneMemClass.one_mem _,
          fun c => by simp only [one_mul, star_one, mul_one]; exact Submodule.subset_span ⟨c, rfl⟩,
          by simp [fullMajMat_one], DiagonalSynthesis.Realizes.one (n + 2)⟩
    | cons p tail ih =>
        intro hp
        have hp0 : p.1 + 1 < 2 * (n + 2) := hp p (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨hG_u, hstG_adj, hG_pres, hG_maj, hG_real⟩ :=
          fullJWAdjGate_preserves_and_majMat n p.1 hp0 p.2
        obtain ⟨U_tail, hUtl_u, hstUtl_adj, hUtl_pres, hUtl_maj, hUtl_real⟩ :=
          ih (fun q hq => hp q (List.mem_cons.mpr (Or.inr hq)))
        let G := unitaryEvolution (finitePauliMatrix (fullJWAdjWord n p.1 hp0)) (-(p.2 / 2))
        refine ⟨G * U_tail, mul_mem hG_u hUtl_u, ?_, ?_, ?_, ?_⟩
        · rw [star_mul]; exact Subalgebra.mul_mem _ hstUtl_adj hstG_adj
        · intro c
          have hexp := eq_sum_fullMajCoeff (hUtl_pres c)
          have h1 : (G * U_tail) * fullJWMajorana n c * star (G * U_tail) =
              ∑ b, (fullMajCoeff n (U_tail * fullJWMajorana n c * star U_tail) b) •
                (G * fullJWMajorana n b * star G) := by
            rw [star_mul]
            calc (G * U_tail) * fullJWMajorana n c * (star U_tail * star G)
                = G * (U_tail * fullJWMajorana n c * star U_tail) * star G := by simp only [mul_assoc]
              _ = G * (∑ b, ((fullMajCoeff n (U_tail * fullJWMajorana n c * star U_tail) b : ℝ) : ℂ) •
                    fullJWMajorana n b) * star G := by rw [← hexp]
              _ = _ := by
                    rw [Matrix.mul_sum, Matrix.sum_mul]
                    exact Finset.sum_congr rfl fun b _ => by rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
          rw [h1]
          exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hG_pres b)
        · rw [fullMajMat_mul hUtl_pres, hG_maj, hUtl_maj, List.map_cons, List.prod_cons]
        · simpa only [List.length_cons, Nat.add_comm] using
            DiagonalSynthesis.Realizes.mul hG_real hUtl_real
  obtain ⟨U_c, hUc_u, hstUc_adj, hUc_pres, hUc_maj, hUc_real⟩ := hcompile L_giv hp_giv
  let W := U_t * star U_c
  have hW_unit : W ∈ unitary (Register (n + 2)) := mul_mem (hUt_unit t) (Unitary.star_mem hUc_u)
  have hW_even : W ∈ evenCliffordSubspace (fullJWMajorana n) :=
    evenCliffordAdjoin_le_subspace' (fullJWMajorana_sq n) (fun _ _ h => fullJWMajorana_anticommute n h)
      (Subalgebra.mul_mem _ (hUt_adjoin t) hstUc_adj)
  have hstUc_pres : ∀ c, star U_c * fullJWMajorana n c * star (star U_c) ∈ fullRealMajoranaSubspace n := by
    intro c
    have hOt_eq_Uc : fullMajMat n U_c = O_t := hUc_maj.trans hOt_prod.symm
    have hlin_comb : fullJWMajorana n c =
        ∑ b, (O_t c b) • (U_c * fullJWMajorana n b * star U_c) := by
      have hterm (b) := eq_sum_fullMajCoeff (hUc_pres b)
      trans (∑ b, (O_t c b) • ∑ a, (fullMajMat n U_c a b) • fullJWMajorana n a)
      · symm
        calc ∑ b, (O_t c b) • ∑ a, (fullMajMat n U_c a b) • fullJWMajorana n a
            = ∑ a, (∑ b, O_t c b * fullMajMat n U_c a b) • fullJWMajorana n a := by
                simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul ..).symm
          _ = ∑ a, ((O_t * O_tᵀ) c a) • fullJWMajorana n a := by rw [hOt_eq_Uc]; rfl
          _ = fullJWMajorana n c := by rw [hOt_orthR]; simp [Matrix.one_apply]
      · refine Finset.sum_congr rfl fun b _ => ?_
        congr 1; rw [hterm b]
        exact Finset.sum_congr rfl fun a _ => by rw [Complex.coe_smul]; rfl
    have hconj_st : star U_c * fullJWMajorana n c * star (star U_c) =
        ∑ b, (O_t c b) • fullJWMajorana n b := by
      conv_lhs => arg 1; arg 2; rw [hlin_comb]
      rw [star_star, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
      calc star U_c * (U_c * fullJWMajorana n b * star U_c) * U_c
          = (star U_c * U_c) * fullJWMajorana n b * (star U_c * U_c) := by simp only [mul_assoc]
        _ = fullJWMajorana n b := by rw [(Unitary.mem_iff.mp hUc_u).1, one_mul, mul_one]
    rw [hconj_st]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hW_pres (c) : W * fullJWMajorana n c * star W ∈ fullRealMajoranaSubspace n := by
    dsimp [W]
    have hexp := eq_sum_fullMajCoeff (hstUc_pres c)
    have h1 : (U_t * star U_c) * fullJWMajorana n c * star (U_t * star U_c) =
        ∑ b, (fullMajCoeff n (star U_c * fullJWMajorana n c * star (star U_c)) b) •
          (U_t * fullJWMajorana n b * star U_t) := by
      rw [star_mul]
      calc (U_t * star U_c) * fullJWMajorana n c * (star (star U_c) * star U_t)
          = U_t * (star U_c * fullJWMajorana n c * star (star U_c)) * star U_t := by simp only [mul_assoc]
        _ = U_t * (∑ b, ((fullMajCoeff n (star U_c * fullJWMajorana n c * star (star U_c)) b : ℝ) : ℂ) •
              fullJWMajorana n b) * star U_t := by rw [← hexp]
        _ = _ := by
              rw [Matrix.mul_sum, Matrix.sum_mul]
              exact Finset.sum_congr rfl fun b _ => by rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
    rw [h1]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hUt_pres t b)
  have hW_maj : fullMajMat n W = 1 := by
    dsimp [W]
    rw [fullMajMat_mul hstUc_pres, fullMajMat_star_eq_transpose, hUc_maj, ← hOt_prod]
    exact hOt_orthR
  have hW_comm (c) : W * fullJWMajorana n c = fullJWMajorana n c * W := by
    have hexp := eq_sum_fullMajCoeff (hW_pres c)
    change W * fullJWMajorana n c * star W =
      ∑ a, ((fullMajMat n W a c : ℝ) : ℂ) • fullJWMajorana n a at hexp
    rw [hW_maj] at hexp
    have hconj1 : W * fullJWMajorana n c * star W = fullJWMajorana n c := by
      rw [hexp, Finset.sum_eq_single c (fun a _ hac => by simp [Matrix.one_apply_ne hac]) (by simp)]
      simp
    calc W * fullJWMajorana n c
        = (W * fullJWMajorana n c * star W) * W := by
            rw [mul_assoc _ (star W) W, (Unitary.mem_iff.mp hW_unit).1, mul_one]
      _ = fullJWMajorana n c * W := by rw [hconj1]
  haveI : Nontrivial (Register (n + 2)) := by
    refine ⟨⟨0, 1, fun h => (zero_ne_one : (0 : ℂ) ≠ 1) ?_⟩⟩
    simpa using congrFun (congrFun h (fun _ => false)) (fun _ => false)
  obtain ⟨z, hz, hW_eq⟩ := eq_scalar_one_of_mem_evenClifford_commutant (fullJWMajorana_sq n)
    (fun _ _ h => fullJWMajorana_anticommute n h) hW_even hW_unit hW_comm
  have hUt_eq_zUc : U_t = z • U_c := by
    calc U_t = U_t * (star U_c * U_c) := by rw [(Unitary.mem_iff.mp hUc_u).1, mul_one]
      _ = W * U_c := (mul_assoc _ _ _).symm
      _ = z • U_c := by rw [hW_eq, Matrix.smul_mul, one_mul]
  have hchoose_eq : (2 * (n + 2)) * (2 * (n + 2) - 1) / 2 = (n + 2) * (2 * n + 3) := by
    have hsub : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
    have h1 : (2 * (n + 2)) * (2 * (n + 2) - 1) = ((n + 2) * (2 * n + 3)) * 2 := by
      rw [hsub]; ring
    rw [h1, Nat.mul_div_cancel _ two_pos]
  obtain ⟨z', hz', C, hC, hUc_eq⟩ := hUc_real
  refine ⟨z * z', by rw [norm_mul, hz, hz', mul_one], C, hC.trans (hlen_giv.trans_eq hchoose_eq), ?_⟩
  change U_t = (z * z') • C.eval.val
  rw [hUt_eq_zUc, hUc_eq, smul_smul]

/-! ### `U(2)^⊗N` local gauge invariance of two-qubit circuit budget `Realizes` -/

private def kronTwoPair (R₁ R₂ : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => R₁ p.1 q.1 * R₂ p.2 q.2

private theorem kronTwoPair_mem_unitary {R₁ R₂ : Matrix Bool Bool ℂ}
    (h₁ : star R₁ * R₁ = 1 ∧ R₁ * star R₁ = 1)
    (h₂ : star R₂ * R₂ = 1 ∧ R₂ * star R₂ = 1) :
    kronTwoPair R₁ R₂ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Unitary.mem_iff]
  have hst : star (kronTwoPair R₁ R₂) =
      fun p q => (star R₁) p.1 q.1 * (star R₂) p.2 q.2 := by
    ext p q; simp [kronTwoPair, star_mul']
  rw [hst]
  constructor <;> ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ <;> simp only [kronTwoPair, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Prod.ext_iff]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        ((star R₁) p₁ x * (star R₂) p₂ y) * (R₁ x q₁ * R₂ y q₂)) =
        ((star R₁ * R₁) p₁ q₁) * ((star R₂ * R₂) p₂ q₂) := by
      simp only [Matrix.mul_apply]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hf, h₁.1, h₂.1, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        (R₁ p₁ x * R₂ p₂ y) * ((star R₁) x q₁ * (star R₂) y q₂)) =
        ((R₁ * star R₁) p₁ q₁) * ((R₂ * star R₂) p₂ q₂) := by
      simp only [Matrix.mul_apply]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hf, h₁.2, h₂.2, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]

private theorem prodLocalMatrix_conj_twoQubitLiftMatrix {N : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (a b : Fin N) (hab : a ≠ b) (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    prodLocalMatrix R * twoQubitLiftMatrix a b hab M * star (prodLocalMatrix R) =
      twoQubitLiftMatrix a b hab (kronTwoPair (R a) (R b) * M * star (kronTwoPair (R a) (R b))) := by
  let W := prodLocalMatrix R
  have hlift_apply (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) (u v : Config N) :
      twoQubitLiftMatrix a b hab X u v =
        if ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r then X (u a, u b) (v a, v b) else 0 := by
    dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.symm_symm]
    change (Matrix.kroneckerMap (· * ·) X 1)
      (splitTwoQubitConfig a b hab u) (splitTwoQubitConfig a b hab v) = _
    rw [Matrix.kroneckerMap_apply]
    by_cases hall : ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r
    · rw [if_pos hall, show (splitTwoQubitConfig a b hab u).2 =
        (splitTwoQubitConfig a b hab v).2 from funext fun ⟨r, hr⟩ => hall r hr.1 hr.2,
        Matrix.one_apply_eq, mul_one]; rfl
    · rw [if_neg hall, Matrix.one_apply_ne (fun heq => hall fun r hra hrb =>
        congrFun heq ⟨r, hra, hrb⟩), mul_zero]
  let pairSet : Finset (Fin N) := {a, b}
  have hfactor (A B : Matrix Bool Bool ℂ) :
      twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) =
        prodLocalMatrix (fun r => if r = a then A else if r = b then B else 1) := by
    ext u v
    rw [hlift_apply]; dsimp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hab]
    simp only [↓reduceIte, hab.symm]
    have hrest : (∏ r ∈ pairSetᶜ,
        (if r = a then A else if r = b then B else 1) (u r) (v r)) =
        if ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r then 1 else 0 := by
      have h1 : ∀ r ∈ pairSetᶜ,
          (if r = a then A else if r = b then B else 1) (u r) (v r) =
            if u r = v r then 1 else 0 := by
        intro r hr
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        simp [hr.1, hr.2, Matrix.one_apply]
      rw [Finset.prod_congr rfl h1]
      by_cases hall : ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r
      · rw [if_pos hall]
        refine Finset.prod_eq_one fun r hr => ?_
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        rw [if_pos (hall r hr.1 hr.2)]
      · rw [if_neg hall]; push Not at hall
        obtain ⟨r, hra, hrb, hne⟩ := hall
        exact Finset.prod_eq_zero (by simp [pairSet, hra, hrb]) (if_neg hne)
    rw [hrest]; split_ifs <;> ring
  have hconj_factor (A B : Matrix Bool Bool ℂ) :
      W * twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) * star W =
        twoQubitLiftMatrix a b hab
          (fun p q => (R a * A * star (R a)) p.1 q.1 * (R b * B * star (R b)) p.2 q.2) := by
    rw [hfactor A B, hfactor (R a * A * star (R a)) (R b * B * star (R b))]
    dsimp only [W]
    rw [prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]
    congr 1; funext r
    by_cases hra : r = a
    · subst hra; simp
    · by_cases hrb : r = b
      · subst hrb; simp [hab.symm]
      · simp [hra, hrb, mul_one, (hR r).2]
  let E₁ (p q : Bool) : Matrix Bool Bool ℂ := fun x y => if x = p ∧ y = q then 1 else 0
  have hM_sum : twoQubitLiftMatrix a b hab M =
      ∑ p : Bool × Bool, ∑ q : Bool × Bool,
        M p q • twoQubitLiftMatrix a b hab (fun r t => E₁ p.1 q.1 r.1 t.1 * E₁ p.2 q.2 r.2 t.2) := by
    ext u v
    rw [hlift_apply, Matrix.sum_apply]
    simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
    by_cases hall : ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r
    · simp only [if_pos hall]
      rw [Finset.sum_eq_single (u a, u b)]
      · rw [Finset.sum_eq_single (v a, v b)]
        · simp [E₁]
        · intro q _ hq
          have h0 : E₁ (u a) q.1 (u a) (v a) * E₁ (u b) q.2 (u b) (v b) = 0 := by
            by_cases h1 : v a = q.1
            · simp [E₁, show v b ≠ q.2 from fun h => hq (Prod.ext h1.symm h.symm)]
            · simp [E₁, h1]
          rw [h0, mul_zero]
        · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        have h0 : E₁ p.1 q.1 (u a) (v a) * E₁ p.2 q.2 (u b) (v b) = 0 := by
          by_cases h1 : u a = p.1
          · simp [E₁, show u b ≠ p.2 from fun h => hp (Prod.ext h1.symm h.symm)]
          · simp [E₁, h1]
        rw [h0, mul_zero]
      · simp
    · simp [if_neg hall]
  change W * twoQubitLiftMatrix a b hab M * star W = _
  have hlhs_sum : W * twoQubitLiftMatrix a b hab M * star W =
      ∑ p : Bool × Bool, ∑ q : Bool × Bool,
        M p q • twoQubitLiftMatrix a b hab
          (fun r t => (R a * E₁ p.1 q.1 * star (R a)) r.1 t.1 *
            (R b * E₁ p.2 q.2 * star (R b)) r.2 t.2) := by
    rw [hM_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj_factor]
  rw [hlhs_sum]
  ext u v
  rw [hlift_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
  by_cases hall : ∀ r : Fin N, r ≠ a → r ≠ b → u r = v r
  · simp only [if_pos hall]
    have hE1 (S₀ : Matrix Bool Bool ℂ) (p₀ q₀ x₀ z₀ : Bool) :
        (S₀ * E₁ p₀ q₀ * star S₀) x₀ z₀ = S₀ x₀ p₀ * (star S₀) q₀ z₀ := by
      simp only [Matrix.mul_apply, Fintype.sum_bool, E₁]; cases p₀ <;> cases q₀ <;> simp
    have hstK (q : Bool × Bool) :
        (star (kronTwoPair (R a) (R b))) q (v a, v b) =
          (star (R a)) q.1 (v a) * (star (R b)) q.2 (v b) := by
      simp [kronTwoPair, star_mul']
    have hrhs : (kronTwoPair (R a) (R b) * M * star (kronTwoPair (R a) (R b)))
        (u a, u b) (v a, v b) =
        ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          M p q * (kronTwoPair (R a) (R b) (u a, u b) p *
            (star (kronTwoPair (R a) (R b))) q (v a, v b)) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hrhs]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hE1, hE1, hstK q]; dsimp only [kronTwoPair]; ring
  · simp [if_neg hall]

private theorem realizes_one_twoQubitLiftMatrix {N : ℕ}
    (a b : Fin N) (hab : a ≠ b) (V : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Realizes 1 (twoQubitLiftMatrix a b hab V.val) := by
  let z_loc := scalarSpecialUnitaryPhase V
  let G_loc := scalarSpecialUnitaryRepresentative V
  have hz_unit : star z_loc * z_loc = 1 := scalarSpecialUnitaryPhase_unitary V
  have hznorm : ‖star z_loc‖ = 1 := by
    have hsq : ‖z_loc‖ * ‖z_loc‖ = 1 := by simpa [norm_mul] using congrArg norm hz_unit
    have hz0 : ‖z_loc‖ = 1 := by nlinarith [norm_nonneg z_loc, sq_nonneg (‖z_loc‖ - 1)]
    simpa using hz0
  refine ⟨star z_loc, hznorm, TwoQubitCircuit.singleOn a b hab G_loc, le_rfl, ?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  have hgate : (twoQubitLift a b hab G_loc : Register N) =
      z_loc • twoQubitLiftMatrix a b hab V.val := by
    ext x y
    simp [G_loc, z_loc, twoQubitLift, twoQubitLiftMatrix, specialUnitaryAsUnitary,
      scalarSpecialUnitaryRepresentative_coe, unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hz_unit, one_smul]

/-- Conjugating any `Realizes s U` unitary by an arbitrary local unitary product
`prodLocalMatrix R ∈ U(2)^⊗N` preserves its exact two-qubit gate budget `s`. -/
theorem realizes_conj_prodLocalMatrix {N : ℕ} (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1) {s : ℕ} {U : Register N}
    (h : Realizes s U) :
    Realizes s (prodLocalMatrix R * U * star (prodLocalMatrix R)) := by
  let W := prodLocalMatrix R
  obtain ⟨hWL, hWR⟩ := Unitary.mem_iff.mp (prodLocalMatrix_mem_unitary R hR)
  obtain ⟨z, hz, C, hC, hU_eq⟩ := h
  have hlist : ∀ L : List (Matrix.unitaryGroup (Config N) ℂ),
      (∀ g ∈ L, Realizes 1 (W * g.val * star W)) →
      Realizes L.length (W * L.prod.val * star W) := by
    intro L hL; induction L with
    | nil =>
        rw [List.length_nil, List.prod_nil, OneMemClass.coe_one, mul_one, hWR]
        exact DiagonalSynthesis.Realizes.one N
    | cons g rest ih =>
        have hsplit : W * (g.val * rest.prod.val) * star W =
            (W * g.val * star W) * (W * rest.prod.val * star W) := by
          calc W * (g.val * rest.prod.val) * star W
              = W * g.val * (star W * W) * rest.prod.val * star W := by
                  rw [hWL, mul_one]; simp only [mul_assoc]
            _ = _ := by simp only [mul_assoc]
        rw [List.length_cons, Nat.add_comm, List.prod_cons, Submonoid.coe_mul, hsplit]
        exact DiagonalSynthesis.Realizes.mul (hL g (List.mem_cons.mpr (Or.inl rfl)))
          (ih fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
  let L_gates : List (Matrix.unitaryGroup (Config N) ℂ) :=
    (List.ofFn fun r => C.architecture.gateLift r (C.gates r)).reverse
  have hmem : ∀ g ∈ L_gates, Realizes 1 (W * g.val * star W) := by
    intro g hg
    rw [List.mem_reverse] at hg
    refine ((List.forall_mem_ofFn_iff
      (P := fun g : Matrix.unitaryGroup (Config N) ℂ =>
        Realizes 1 (W * g.val * star W))).mpr fun r => ?_) g hg
    let a := (C.architecture.sites r).1
    let b := (C.architecture.sites r).2
    let hab := C.architecture.distinct r
    let G0 := C.gates r
    have hlift_val : (C.architecture.gateLift r G0).val =
        twoQubitLiftMatrix a b hab (specialUnitaryAsUnitary G0).val := by
      ext x y
      simp only [TwoQubitArchitecture.gateLift, twoQubitLift, twoQubitLiftMatrix,
        unitaryGroupReindex_coe, Quantum.tensorGate_val, OneMemClass.coe_one,
        Matrix.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply, a, b, G0]
    have hK_u := kronTwoPair_mem_unitary (hR a) (hR b)
    rw [hlift_val, prodLocalMatrix_conj_twoQubitLiftMatrix R hR a b hab]
    exact realizes_one_twoQubitLiftMatrix a b hab
      ⟨kronTwoPair (R a) (R b) * (specialUnitaryAsUnitary G0).val * star (kronTwoPair (R a) (R b)),
        mul_mem (mul_mem hK_u (specialUnitaryAsUnitary G0).2) (Unitary.star_mem hK_u)⟩
  have hlen : L_gates.length = C.gateCount := by simp [L_gates]
  have hprod_eq : L_gates.prod = C.eval := rfl
  obtain ⟨z', hz', C', hC', heq'⟩ := hlen ▸ hprod_eq ▸ hlist L_gates hmem
  refine ⟨z * z', by rw [norm_mul, hz, hz', mul_one], C', hC'.trans hC, ?_⟩
  change W * U * star W = _
  rw [hU_eq, Matrix.mul_smul, Matrix.smul_mul, heq', smul_smul]

/-- Exact `choose(2N, 2) = (n + 2) * (2 * n + 3)`-gate compilation for **every** locally rotated
`(5N - 4)`-parameter matchgate chain `W H(v) W*` (`W = prodLocalMatrix R ∈ U(2)^⊗N`) for all
`t ∈ ℝ`. -/
theorem realizes_choose_twoN_of_locallyRotatedMatchgate {n : ℕ} (v : PathShell n)
    (hv : ∀ l : PathLabel n, ¬ isMatchgateChainLabel l → v l = 0)
    (R : Fin (n + 2) → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1) (t : ℝ) :
    let W := prodLocalMatrix R
    Realizes ((n + 2) * (2 * n + 3)) (unitaryEvolution (W * pathHamiltonian v * star W) t) := by
  intro W
  have hW_u : W ∈ unitary (Register (n + 2)) := prodLocalMatrix_mem_unitary R hR
  let W_ug : Matrix.unitaryGroup (Config (n + 2)) ℂ := ⟨W, hW_u⟩
  have hc := unitaryEvolution_conj W (pathHamiltonian v) (Unitary.isUnit_coe (U := W_ug)) t
  rw [inv_eq_star_of_mem_unitary hW_u] at hc
  rw [hc]
  exact realizes_conj_prodLocalMatrix R hR (realizes_choose_twoN_of_matchgateChain v hv t)

/-! ## Section 2: Hidden rotated matchgate survival tube inside `allCoordStrongEvent ∩ bondRankTwoEvent` -/

private theorem pythRotMat_orthog' :
    pythRotMatᵀ * pythRotMat = 1 ∧ pythRotMat * pythRotMatᵀ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pythRotMat, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

private theorem pythRotMat_col2_ge' (a : Fin 3) : 1 / 3 ≤ pythRotMat a 2 := by
  fin_cases a <;> simp [pythRotMat] <;> norm_num

private theorem pythRotMat_entry_abs_le' (a b : Fin 3) : |pythRotMat a b| ≤ 1 := by
  fin_cases a <;> fin_cases b <;> simp [pythRotMat] <;> norm_num

private theorem pythRotMat_mg_sum_abs_ge' (a₁ a₂ : Fin 3) :
    2 / 9 ≤ |pythRotMat a₁ 0 * pythRotMat a₂ 0 + pythRotMat a₁ 1 * pythRotMat a₂ 1| := by
  fin_cases a₁ <;> fin_cases a₂ <;> simp [pythRotMat] <;> norm_num

private theorem pythUnitary_unitary' :
    star pythUnitary * pythUnitary = 1 ∧ pythUnitary * star pythUnitary = 1 := by
  let pythInt : Matrix Bool Bool ℂ := fun x y =>
    match x, y with
    | false, false => 2 | false, true => -1 + Complex.I
    | true, false => 1 + Complex.I | true, true => 2
  have hdef : pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • pythInt := by
    ext x y; fin_cases x <;> fin_cases y <;> rfl
  have hsq : (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ)) = (1 / 6 : ℂ) := by
    have h1 : (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 / 6 := by
      rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, h1]; norm_num
  have hst : star pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • star pythInt := by
    rw [hdef, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hint1 : star pythInt * pythInt = (6 : ℂ) • 1 := by
    ext x y; fin_cases x <;> fin_cases y <;>
      simp [pythInt, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.smul_apply, map_ofNat] <;>
      norm_num [Complex.ext_iff]
  have hint2 : pythInt * star pythInt = (6 : ℂ) • 1 := by
    ext x y; fin_cases x <;> fin_cases y <;>
      simp [pythInt, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.smul_apply, map_ofNat] <;>
      norm_num [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [hst, hdef, smul_mul_smul_comm, hsq, hint1, smul_smul]; norm_num
  · rw [hst, hdef, smul_mul_smul_comm, hsq, hint2, smul_smul]; norm_num

private theorem pythUnitary_conj_pauli' (b : Fin 3) :
    pythUnitary * finiteQubitPauli b * star pythUnitary =
      ∑ a : Fin 3, ((pythRotMat a b : ℝ) : ℂ) • finiteQubitPauli a := by
  let pythInt : Matrix Bool Bool ℂ := fun x y =>
    match x, y with
    | false, false => 2 | false, true => -1 + Complex.I
    | true, false => 1 + Complex.I | true, true => 2
  have hdef : pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • pythInt := by
    ext x y; fin_cases x <;> fin_cases y <;> rfl
  have hsq : (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ)) = (1 / 6 : ℂ) := by
    have h1 : (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 / 6 := by
      rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, h1]; norm_num
  have hst : star pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • star pythInt := by
    rw [hdef, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hmul : pythUnitary * finiteQubitPauli b * star pythUnitary =
      (1 / 6 : ℂ) • (pythInt * finiteQubitPauli b * star pythInt) := by
    rw [hst, hdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsq]
  rw [hmul]
  fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pythInt, pythRotMat, finiteQubitPauli, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_ofNat] <;>
    norm_num [Complex.ext_iff]

private theorem sum4_comm' {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
  calc ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d
      = ∑ a : α, ∑ c : γ, ∑ b : β, ∑ d : δ, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, ∑ d : δ, f a b c d := Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ d : δ, ∑ b : β, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem pythShellInv_left' (n : ℕ) (z : PathLabel n → ℝ) :
    pythShellInv n (pythShellMap n z) = z := by
  obtain ⟨hL, _⟩ := pythRotMat_orthog'
  have hcol (b₁ b₂ : Fin 3) : (∑ a : Fin 3, pythRotMat a b₁ * pythRotMat a b₂) =
      if b₁ = b₂ then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrFun (congrFun hL b₁) b₂
  funext l
  rcases l with ⟨v, b⟩ | ⟨e, ⟨b₁, b₂⟩⟩
  · simp only [pythShellInv, pythShellMap, Finset.mul_sum]; rw [Finset.sum_comm]
    have hs : (∑ c : Fin 3, ∑ a : Fin 3, pythRotMat a b * (pythRotMat a c * z (.inl (v, c)))) =
        ∑ c : Fin 3, (∑ a : Fin 3, pythRotMat a b * pythRotMat a c) * z (.inl (v, c)) :=
      Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hs]; simp_rw [hcol b]; simp
  · simp only [pythShellInv, pythShellMap]
    have hfact : (∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
        pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
          ∑ c₁ : Fin 3, ∑ c₂ : Fin 3, pythRotMat a₁ c₁ * pythRotMat a₂ c₂ * z (.inr (e, (c₁, c₂)))) =
        ∑ c₁ : Fin 3, ∑ c₂ : Fin 3,
          (∑ a₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₁ c₁) *
            (∑ a₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat a₂ c₂) * z (.inr (e, (c₁, c₂))) := by
      calc _ = ∑ a₁ : Fin 3, ∑ a₂ : Fin 3, ∑ c₁ : Fin 3, ∑ c₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat a₁ c₁ * pythRotMat a₂ c₂ * z (.inr (e, (c₁, c₂)))) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum ..
        _ = _ := (sum4_comm' _).trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
              rw [Finset.sum_mul, Finset.sum_mul]
              exact Finset.sum_congr rfl fun _ _ => by
                rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring)
    rw [hfact]; simp_rw [hcol b₁, hcol b₂]; simp

private theorem pythShellInv_right' (n : ℕ) (x_lbl : PathLabel n → ℝ) :
    pythShellMap n (pythShellInv n x_lbl) = x_lbl := by
  obtain ⟨_, hR⟩ := pythRotMat_orthog'
  have hrow (a₁ a₂ : Fin 3) : (∑ b : Fin 3, pythRotMat a₁ b * pythRotMat a₂ b) =
      if a₁ = a₂ then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrFun (congrFun hR a₁) a₂
  funext l
  rcases l with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
  · simp only [pythShellMap, pythShellInv, Finset.mul_sum]; rw [Finset.sum_comm]
    have hs : (∑ d : Fin 3, ∑ b : Fin 3, pythRotMat a b * (pythRotMat d b * x_lbl (.inl (v, d)))) =
        ∑ d : Fin 3, (∑ b : Fin 3, pythRotMat a b * pythRotMat d b) * x_lbl (.inl (v, d)) :=
      Finset.sum_congr rfl fun d _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hs]; simp_rw [hrow a]; simp
  · simp only [pythShellMap, pythShellInv]
    have hfact : (∑ b₁ : Fin 3, ∑ b₂ : Fin 3,
        pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
          ∑ d₁ : Fin 3, ∑ d₂ : Fin 3, pythRotMat d₁ b₁ * pythRotMat d₂ b₂ * x_lbl (.inr (e, (d₁, d₂)))) =
        ∑ d₁ : Fin 3, ∑ d₂ : Fin 3,
          (∑ b₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat d₁ b₁) *
            (∑ b₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat d₂ b₂) * x_lbl (.inr (e, (d₁, d₂))) := by
      calc _ = ∑ b₁ : Fin 3, ∑ b₂ : Fin 3, ∑ d₁ : Fin 3, ∑ d₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat d₁ b₁ * pythRotMat d₂ b₂ * x_lbl (.inr (e, (d₁, d₂)))) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum ..
        _ = _ := (sum4_comm' _).trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
              rw [Finset.sum_mul, Finset.sum_mul]
              exact Finset.sum_congr rfl fun _ _ => by
                rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring)
    rw [hfact]; simp_rw [hrow a₁, hrow a₂]; simp

private theorem pythShellMap_measurePreserving' (n : ℕ) :
    MeasurePreserving (pythShellMap n)
      (Measure.pi fun _ : PathLabel n => gaussianReal 0 1)
      (Measure.pi fun _ : PathLabel n => gaussianReal 0 1) := by
  let O_blk : Matrix (PathLabel n) (PathLabel n) ℝ := fun l₁ l₂ =>
    match l₁, l₂ with
    | .inl (v₁, a), .inl (v₂, b) => if v₁ = v₂ then pythRotMat a b else 0
    | .inr (e₁, (a₁, a₂)), .inr (e₂, (b₁, b₂)) =>
        if e₁ = e₂ then pythRotMat a₁ b₁ * pythRotMat a₂ b₂ else 0
    | _, _ => 0
  have hmul_eq (u : PathLabel n → ℝ) : pythShellMap n u = O_blk *ᵥ u := by
    funext l; rcases l with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
    · simp only [pythShellMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
      rw [show (∑ x : Fin (n + 1), ∑ x_1 : Fin 3, ∑ y : Fin 3,
          O_blk (.inl (v, a)) (.inr (x, (x_1, y))) * u (.inr (x, (x_1, y)))) = 0
        by simp [O_blk], add_zero, Finset.sum_eq_single v (fun v' _ hne => by simp [O_blk, hne.symm]) (by simp)]
      simp [O_blk]
    · simp only [pythShellMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
      rw [show (∑ x : Fin (n + 2), ∑ y : Fin 3, O_blk (.inr (e, (a₁, a₂))) (.inl (x, y)) * u (.inl (x, y))) = 0
        by simp [O_blk], zero_add, Finset.sum_eq_single e (fun e' _ hne => by simp [O_blk, hne.symm]) (by simp)]
      simp [O_blk]
  obtain ⟨hL, hR⟩ := pythRotMat_orthog'
  have hcol (b₁ b₂ : Fin 3) : (∑ a : Fin 3, pythRotMat a b₁ * pythRotMat a b₂) =
      if b₁ = b₂ then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using congrFun (congrFun hL b₁) b₂
  have hrow (a₁ a₂ : Fin 3) : (∑ b : Fin 3, pythRotMat a₁ b * pythRotMat a₂ b) =
      if a₁ = a₂ then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using congrFun (congrFun hR a₁) a₂
  have hO_left : O_blkᵀ * O_blk = 1 := by
    ext l₁ l₂
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.one_apply]
    rcases l₁ with ⟨v₁, b₁⟩ | ⟨e₁, ⟨b₁, b₂⟩⟩ <;> rcases l₂ with ⟨v₂, c₁⟩ | ⟨e₂, ⟨c₁, c₂⟩⟩
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, add_zero]
      by_cases hv : v₁ = v₂
      · subst hv; rw [Finset.sum_eq_single v₁ (fun _ _ hne => by simp [hne]) (by simp)]
        simp [hcol b₁ c₁, Prod.ext_iff]
      · rw [if_neg (by simp [hv])]
        exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun _ _ => by
          by_cases h1 : v = v₁ <;> [subst h1; skip] <;> simp [*]
    · simp [O_blk]
    · simp [O_blk]
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, zero_add]
      by_cases he : e₁ = e₂
      · subst he; rw [Finset.sum_eq_single e₁ (fun _ _ hne => by simp [hne]) (by simp)]
        simp only [↓reduceIte]
        have hf : (∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
            (pythRotMat a₁ b₁ * pythRotMat a₂ b₂) * (pythRotMat a₁ c₁ * pythRotMat a₂ c₂)) =
            (∑ a₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₁ c₁) *
              (∑ a₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat a₂ c₂) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [hf, hcol b₁ c₁, hcol b₂ c₂]
        by_cases h1 : b₁ = c₁ <;> by_cases h2 : b₂ = c₂ <;> simp [h1, h2]
      · rw [if_neg (by simp [he])]
        exact Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun _ _ => by
          by_cases h1 : e = e₁ <;> [subst h1; skip] <;> simp [*]
  have hO_right : O_blk * O_blkᵀ = 1 := by
    ext l₁ l₂
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.one_apply]
    rcases l₁ with ⟨v₁, a₁⟩ | ⟨e₁, ⟨a₁, a₂⟩⟩ <;> rcases l₂ with ⟨v₂, d₁⟩ | ⟨e₂, ⟨d₁, d₂⟩⟩
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, add_zero]
      by_cases hv : v₁ = v₂
      · subst hv; rw [Finset.sum_eq_single v₁ (fun _ _ hne => by simp [hne.symm]) (by simp)]
        simp [hrow a₁ d₁, Prod.ext_iff]
      · rw [if_neg (by simp [hv])]
        exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun _ _ => by
          by_cases h1 : v = v₁
          · subst h1; simp [Ne.symm hv]
          · simp [Ne.symm h1]
    · simp [O_blk]
    · simp [O_blk]
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, zero_add]
      by_cases he : e₁ = e₂
      · subst he; rw [Finset.sum_eq_single e₁ (fun _ _ hne => by simp [hne.symm]) (by simp)]
        simp only [↓reduceIte]
        have hf : (∑ b₁ : Fin 3, ∑ b₂ : Fin 3,
            (pythRotMat a₁ b₁ * pythRotMat a₂ b₂) * (pythRotMat d₁ b₁ * pythRotMat d₂ b₂)) =
            (∑ b₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat d₁ b₁) *
              (∑ b₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat d₂ b₂) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [hf, hrow a₁ d₁, hrow a₂ d₂]
        by_cases h1 : a₁ = d₁ <;> by_cases h2 : a₂ = d₂ <;> simp [h1, h2]
      · rw [if_neg (by simp [he])]
        exact Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun _ _ => by
          by_cases h1 : e = e₁
          · subst h1; simp [Ne.symm he]
          · simp [Ne.symm h1]
  rw [show pythShellMap n = fun u => O_blk *ᵥ u from funext hmul_eq]
  exact measurePreserving_pi_gaussian_orthogonal O_blk hO_left hO_right

theorem prodLocalMatrix_conj_pathHamiltonian {n : ℕ}
    (S_loc : Fin (n + 2) → Matrix Bool Bool ℂ)
    (O_S : Fin (n + 2) → Matrix (Fin 3) (Fin 3) ℝ)
    (hS_unit : ∀ s, S_loc s * star (S_loc s) = 1)
    (hS_pauli : ∀ (s : Fin (n + 2)) (b : Fin 3),
      S_loc s * finiteQubitPauli b * star (S_loc s) =
        ∑ a : Fin 3, ((O_S s a b : ℝ) : ℂ) • finiteQubitPauli a)
    (u u_rot : PathShell n)
    (hu_site : ∀ (v : Fin (n + 2)) (a : Fin 3),
      u_rot (.inl (v, a)) = ∑ b : Fin 3, O_S v a b * u (.inl (v, b)))
    (hu_bond : ∀ (e : Fin (n + 1)) (a₁ a₂ : Fin 3),
      u_rot (.inr (e, (a₁, a₂))) =
        ∑ b₁ : Fin 3, ∑ b₂ : Fin 3, O_S e.castSucc a₁ b₁ * O_S e.succ a₂ b₂ * u (.inr (e, (b₁, b₂)))) :
    prodLocalMatrix S_loc * pathHamiltonian u * star (prodLocalMatrix S_loc) =
      pathHamiltonian u_rot := by
  let W := prodLocalMatrix S_loc
  have honsite (v : Fin (n + 2)) (b : Fin 3) :
      W * finitePauliMatrix (onsiteWord v b) * star W =
        ∑ a : Fin 3, ((O_S v a b : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a) := by
    rw [prodLocalMatrix_conj_pauli]; ext x y; rw [Matrix.sum_apply]; simp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    have hrest : (∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ,
        (S_loc s * boolPauliOption (onsiteWord v b s) * star (S_loc s)) (x s) (y s)) =
        ∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ, boolPauliOptionEntry none (x s, y s) :=
      Finset.prod_congr rfl fun s hs => by
        have hsv : s ≠ v := by simpa using hs
        simp [onsiteWord, hsv, boolPauliOption, boolPauliOptionEntry, hS_unit s, Matrix.one_apply]
    rw [show boolPauliOption (onsiteWord v b v) = finiteQubitPauli b by simp [onsiteWord, boolPauliOption],
      hS_pauli v b, hrest, Matrix.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]; congr 1
    unfold finitePauliMatrix
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    congr 1
    · simp [onsiteWord, boolPauliOptionEntry, boolPauliOption]
    · exact Finset.prod_congr rfl fun s hs => by simp [onsiteWord, show s ≠ v by simpa using hs]
  have hcoupling (e : Fin (n + 1)) (b₁ b₂ : Fin 3) :
      W * finitePauliMatrix (couplingWord e (b₁, b₂)) * star W =
        ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
          ((O_S e.castSucc a₁ b₁ * O_S e.succ a₂ b₂ : ℝ) : ℂ) • finitePauliMatrix (couplingWord e (a₁, a₂)) := by
    rw [prodLocalMatrix_conj_pauli]; ext x y
    simp only [prodLocalMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    let pairSet : Finset (Fin (n + 2)) := {e.castSucc, e.succ}
    have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
    have hrest : (∏ s ∈ pairSetᶜ,
        (S_loc s * boolPauliOption (couplingWord e (b₁, b₂) s) * star (S_loc s)) (x s) (y s)) =
        ∏ s ∈ pairSetᶜ, boolPauliOptionEntry none (x s, y s) :=
      Finset.prod_congr rfl fun s hs => by
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        simp [couplingWord, hs.1, hs.2, boolPauliOption, boolPauliOptionEntry, hS_unit s, Matrix.one_apply]
    rw [show boolPauliOption (couplingWord e (b₁, b₂) e.castSucc) = finiteQubitPauli b₁ by
        simp [couplingWord, boolPauliOption],
      show boolPauliOption (couplingWord e (b₁, b₂) e.succ) = finiteQubitPauli b₂ by
        simp [couplingWord, hne_cs.symm, boolPauliOption],
      hS_pauli e.castSucc b₁, hS_pauli e.succ b₂, hrest,
      Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    have hfp : finitePauliMatrix (couplingWord e (a₁, a₂)) x y =
        finiteQubitPauli a₁ (x e.castSucc) (y e.castSucc) *
          finiteQubitPauli a₂ (x e.succ) (y e.succ) *
          ∏ s ∈ pairSetᶜ, boolPauliOptionEntry none (x s, y s) := by
      unfold finitePauliMatrix
      rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
      congr 1; congr 1
      · simp [couplingWord, boolPauliOptionEntry, boolPauliOption]
      · simp [couplingWord, hne_cs.symm, boolPauliOptionEntry, boolPauliOption]
      · exact Finset.prod_congr rfl fun s hs => by
          simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
          simp [couplingWord, hs.1, hs.2]
    rw [hfp]; ring
  rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun v _ => ?_
    trans (∑ b : Fin 3, ∑ a : Fin 3,
      (((O_S v a b * u (.inl (v, b)) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a)))
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, show pathWord (.inl (v, b)) = onsiteWord v b from rfl,
        honsite v b, Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, Complex.ofReal_mul, mul_comm]
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => by
        rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← hu_site v a]; rfl
  · refine Finset.sum_congr rfl fun e _ => ?_
    trans (∑ b₁ : Fin 3, ∑ b₂ : Fin 3, ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
      (((O_S e.castSucc a₁ b₁ * O_S e.succ a₂ b₂ * u (.inr (e, (b₁, b₂))) : ℝ) : ℂ) •
        finitePauliMatrix (couplingWord e (a₁, a₂))))
    · refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul,
        show pathWord (.inr (e, (b₁, b₂))) = couplingWord e (b₁, b₂) from rfl,
        hcoupling e b₁ b₂, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a₂ _ => by rw [smul_smul]; congr 1; push_cast; ring
    · rw [sum4_comm']
      exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => by
        simp_rw [← Finset.sum_smul, ← Complex.ofReal_sum]
        rw [← hu_bond e a₁ a₂]; rfl

private theorem prodPyth_conj_pathHamiltonian' {n : ℕ} (u : PathShell n) :
    prodLocalMatrix (fun _ : Fin (n + 2) => pythUnitary) * pathHamiltonian u *
      star (prodLocalMatrix (fun _ : Fin (n + 2) => pythUnitary)) =
      pathHamiltonian (WithLp.toLp 2 (pythShellMap n u.ofLp)) :=
  prodLocalMatrix_conj_pathHamiltonian
    (fun _ : Fin (n + 2) => pythUnitary) (fun _ : Fin (n + 2) => pythRotMat)
    (fun _ => pythUnitary_unitary'.2) (fun _ b => pythUnitary_conj_pauli' b)
    u (WithLp.toLp 2 (pythShellMap n u.ofLp)) (fun _ _ => rfl) (fun _ _ _ => rfl)

private def isStrongMatchgateLabel {n : ℕ} : PathLabel n → Prop
  | .inl (_, a) => a = 2
  | .inr (_, (p, q)) => (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 1)

private instance {n : ℕ} (l : PathLabel n) : Decidable (isStrongMatchgateLabel l) := by
  cases l with
  | inl va => dsimp [isStrongMatchgateLabel]; infer_instance
  | inr epq => rcases epq with ⟨e, p, q⟩; dsimp [isStrongMatchgateLabel]; infer_instance

private theorem card_filter_matchgateChainLabel (k : ℕ) :
    (Finset.univ.filter (@isMatchgateChainLabel (k + 1))).card = 5 * k + 11 := by
  have hbij : (Finset.univ.filter isMatchgateChainLabel : Finset (PathLabel (k + 1))).card =
      (Finset.univ : Finset (Fin (k + 3))).card + 4 * (Finset.univ : Finset (Fin (k + 2))).card := by
    let siteSet : Finset (PathLabel (k + 1)) :=
      Finset.univ.map ⟨fun v : Fin (k + 3) => .inl (v, 2), fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1⟩
    let bondPairs : Finset (Fin 3 × Fin 3) := {(0, 0), (0, 1), (1, 0), (1, 1)}
    have hbp4 : bondPairs.card = 4 := by decide
    let bondSet : Finset (PathLabel (k + 1)) :=
      (Finset.univ ×ˢ bondPairs).map ⟨fun epq : Fin (k + 2) × (Fin 3 × Fin 3) => .inr epq,
        fun _ _ h => Sum.inr.inj h⟩
    have hdis : Disjoint siteSet bondSet := by
      refine Finset.disjoint_left.mpr fun l h1 h2 => ?_
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp h1
      obtain ⟨epq, _, heq⟩ := Finset.mem_map.mp h2
      exact nomatch heq
    have hun : (Finset.univ.filter isMatchgateChainLabel : Finset (PathLabel (k + 1))) =
        siteSet ∪ bondSet := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, siteSet, bondSet,
        Finset.mem_map, Finset.mem_product, bondPairs, Finset.mem_insert, Finset.mem_singleton,
        Function.Embedding.coeFn_mk]
      rcases l with ⟨v, a⟩ | ⟨e, ⟨p, q⟩⟩
      · simp only [isMatchgateChainLabel]
        exact ⟨fun h => Or.inl ⟨v, h ▸ rfl⟩, fun h => by
          rcases h with ⟨v', hv⟩ | ⟨epq, _, hc⟩
          · exact (Prod.mk.inj (Sum.inl.inj hv)).2.symm
          · exact nomatch hc⟩
      · simp only [isMatchgateChainLabel]
        constructor
        · rintro ⟨hp, hq⟩
          right; refine ⟨(e, (p, q)), ?_, rfl⟩
          have hp01 : p = 0 ∨ p = 1 := by clear * - hp; revert p hp; decide
          have hq01 : q = 0 ∨ q = 1 := by clear * - hq; revert q hq; decide
          rcases hp01 with rfl | rfl <;> rcases hq01 with rfl | rfl <;> simp
        · rintro (⟨v', hv⟩ | ⟨⟨e', p', q'⟩, hpq, heq⟩)
          · exact nomatch hv
          · obtain ⟨rfl, rfl, rfl⟩ : e' = e ∧ p' = p ∧ q' = q := by
              have h1 := Prod.mk.inj (Sum.inr.inj heq)
              exact ⟨h1.1, (Prod.mk.inj h1.2).1, (Prod.mk.inj h1.2).2⟩
            rcases hpq with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> decide
    rw [hun, Finset.card_union_of_disjoint hdis]
    simp [siteSet, bondSet, Finset.card_product, hbp4, mul_comm]
  rw [hbij]; simp only [Finset.card_univ, Fintype.card_fin]; omega

private theorem card_filter_strongMatchgateLabel (k : ℕ) :
    (Finset.univ.filter (@isStrongMatchgateLabel (k + 1))).card = 3 * k + 7 := by
  let siteSet : Finset (PathLabel (k + 1)) :=
    Finset.univ.map ⟨fun v : Fin (k + 3) => .inl (v, 2), fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1⟩
  let diagPairs : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 1)}
  have hdp2 : diagPairs.card = 2 := by decide
  let bondSet : Finset (PathLabel (k + 1)) :=
    (Finset.univ ×ˢ diagPairs).map ⟨fun epq : Fin (k + 2) × (Fin 3 × Fin 3) => .inr epq,
      fun _ _ h => Sum.inr.inj h⟩
  have hdis : Disjoint siteSet bondSet := by
    refine Finset.disjoint_left.mpr fun l h1 h2 => ?_
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp h1
    obtain ⟨epq, _, heq⟩ := Finset.mem_map.mp h2
    exact nomatch heq
  have hun : (Finset.univ.filter (@isStrongMatchgateLabel (k + 1))) = siteSet ∪ bondSet := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, siteSet,
      bondSet, Finset.mem_map, Finset.mem_product, diagPairs, Finset.mem_insert,
      Finset.mem_singleton, Function.Embedding.coeFn_mk]
    rcases l with ⟨v, a⟩ | ⟨e, ⟨p, q⟩⟩
    · simp only [isStrongMatchgateLabel]
      exact ⟨fun h => Or.inl ⟨v, h ▸ rfl⟩, fun h => by
        rcases h with ⟨v', hv⟩ | ⟨epq, _, hc⟩
        · exact (Prod.mk.inj (Sum.inl.inj hv)).2.symm
        · exact nomatch hc⟩
    · simp only [isStrongMatchgateLabel]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact Or.inr ⟨(e, (0, 0)), Or.inl rfl, rfl⟩
        · exact Or.inr ⟨(e, (1, 1)), Or.inr rfl, rfl⟩
      · rintro (⟨v', hv⟩ | ⟨⟨e', p', q'⟩, hpq, heq⟩)
        · exact nomatch hv
        · have h1 := Prod.mk.inj (Sum.inr.inj heq)
          obtain ⟨rfl, rfl, rfl⟩ : e' = e ∧ p' = p ∧ q' = q :=
            ⟨h1.1, (Prod.mk.inj h1.2).1, (Prod.mk.inj h1.2).2⟩
          rcases hpq with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
  rw [hun, Finset.card_union_of_disjoint hdis]
  simp only [siteSet, bondSet, Finset.card_map, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, hdp2]; omega

private theorem bond_sum_decomp_aux (u₁ u₂ : Fin 3 → ℝ) (f : Fin 3 × Fin 3 → ℝ) (M : ℝ) :
    (∑ b₁ : Fin 3, ∑ b₂ : Fin 3, u₁ b₁ * u₂ b₂ * f (b₁, b₂)) =
      M * (u₁ 0 * u₂ 0 + u₁ 1 * u₂ 1) +
      ∑ pq : Fin 3 × Fin 3, u₁ pq.1 * u₂ pq.2 *
        (f pq - if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then M else 0) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  dsimp only
  rw [if_pos (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  ring

private theorem pythRotMat_bond_decomp' (f : Fin 3 × Fin 3 → ℝ) (M : ℝ) (a₁ a₂ : Fin 3) :
    (∑ b₁ : Fin 3, ∑ b₂ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₂ b₂ * f (b₁, b₂)) =
      M * (pythRotMat a₁ 0 * pythRotMat a₂ 0 + pythRotMat a₁ 1 * pythRotMat a₂ 1) +
      ∑ pq : Fin 3 × Fin 3, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 *
        (f pq - if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then M else 0) :=
  bond_sum_decomp_aux (pythRotMat a₁) (pythRotMat a₂) f M

private theorem pythTube_mem_strong_and_rankTwo (k : ℕ) (η δ : ℝ) (hδ_le : δ ≤ 1 / 200)
    (u u_tilde : PathShell (k + 1)) (hu_ofLp : u.ofLp = pythShellMap (k + 1) u_tilde.ofLp)
    (hsite : ∀ v : Fin (k + 3),
      u_tilde (.inl (v, 2)) ∈ Icc (9 * |η| + 18) (9 * |η| + 18 + 1 / 20) ∧
      |u_tilde (.inl (v, 0))| ≤ δ ∧ |u_tilde (.inl (v, 1))| ≤ δ)
    (hbond_diag : ∀ e : Fin (k + 2),
      9 * |η| + 18 ≤ u_tilde (.inr (e, (0, 0))) ∧ 9 * |η| + 18 ≤ u_tilde (.inr (e, (1, 1))))
    (hbond_rem : ∀ (e : Fin (k + 2)) (pq : Fin 3 × Fin 3),
      |u_tilde (.inr (e, pq)) -
        (if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then 9 * |η| + 18 else 0)| ≤ 1 / 20) :
    (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ allCoordStrongEvent (k + 1) η ∧
    (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ bondRankTwoEvent (k + 1) η ∧
    3 ≤ |u (.inl (0, 2))| := by
  let M_η : ℝ := 9 * |η| + 18
  have hM_ge18 : 18 ≤ M_η := by have hnn := abs_nonneg η; dsimp [M_η]; linarith only [hnn]
  have hM_nn : 0 ≤ M_η := by linarith only [hM_ge18]
  let c_mg (a₁ a₂ : Fin 3) : ℝ :=
    pythRotMat a₁ 0 * pythRotMat a₂ 0 + pythRotMat a₁ 1 * pythRotMat a₂ 1
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change η ≤ |u (pathCoeffEquiv (k + 1) i)|
    rw [show u (pathCoeffEquiv (k + 1) i) = pythShellMap (k + 1) u_tilde.ofLp (pathCoeffEquiv (k + 1) i)
      from congrFun hu_ofLp _]
    rcases pathCoeffEquiv (k + 1) i with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
    · obtain ⟨hz, hx, hy⟩ := hsite v
      have hval_eq : pythShellMap (k + 1) u_tilde.ofLp (.inl (v, a)) =
          pythRotMat a 0 * u_tilde (.inl (v, 0)) +
          pythRotMat a 1 * u_tilde (.inl (v, 1)) +
          pythRotMat a 2 * u_tilde (.inl (v, 2)) := by
        simp [pythShellMap, Fin.sum_univ_three]
      have h0_bd : -δ ≤ pythRotMat a 0 * u_tilde (.inl (v, 0)) := by
        have h := mul_le_mul (pythRotMat_entry_abs_le' a 0) hx (abs_nonneg _) zero_le_one
        rw [← abs_mul, one_mul] at h; exact (abs_le.mp h).1
      have h1_bd : -δ ≤ pythRotMat a 1 * u_tilde (.inl (v, 1)) := by
        have h := mul_le_mul (pythRotMat_entry_abs_le' a 1) hy (abs_nonneg _) zero_le_one
        rw [← abs_mul, one_mul] at h; exact (abs_le.mp h).1
      have h2_bd : (1 / 3 : ℝ) * M_η ≤ pythRotMat a 2 * u_tilde (.inl (v, 2)) :=
        mul_le_mul (pythRotMat_col2_ge' a) hz.1 hM_nn (le_trans (by norm_num) (pythRotMat_col2_ge' a))
      have hpos_val : η ≤ pythShellMap (k + 1) u_tilde.ofLp (.inl (v, a)) := by
        dsimp [M_η] at h2_bd
        linarith only [hval_eq, h0_bd, h1_bd, h2_bd, hδ_le, le_abs_self η, abs_nonneg η]
      exact hpos_val.trans (le_abs_self _)
    · let rem (pq : Fin 3 × Fin 3) : ℝ :=
        u_tilde (.inr (e, pq)) -
          (if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then M_η else 0)
      have hdecomp : pythShellMap (k + 1) u_tilde.ofLp (.inr (e, (a₁, a₂))) =
          M_η * c_mg a₁ a₂ +
            ∑ pq : Fin 3 × Fin 3, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq :=
        pythRotMat_bond_decomp' (fun pq => u_tilde (.inr (e, pq))) M_η a₁ a₂
      have hrem_abs : |∑ pq : Fin 3 × Fin 3, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq| ≤
          9 / 20 := by
        calc |∑ pq : Fin 3 × Fin 3, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq|
            ≤ ∑ pq : Fin 3 × Fin 3, |pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _pq : Fin 3 × Fin 3, (1 / 20 : ℝ) := by
              refine Finset.sum_le_sum fun pq _ => ?_
              rw [abs_mul, abs_mul]
              have hc1 : |pythRotMat a₁ pq.1| * |pythRotMat a₂ pq.2| ≤ 1 :=
                (mul_le_mul (pythRotMat_entry_abs_le' a₁ pq.1) (pythRotMat_entry_abs_le' a₂ pq.2)
                  (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
              exact (mul_le_mul hc1 (hbond_rem e pq) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
          _ = 9 / 20 := by
              have hc9 : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by decide
              rw [Finset.sum_const, hc9, nsmul_eq_mul]; norm_num
      have hmain_abs : (2 / 9 : ℝ) * M_η ≤ |M_η * c_mg a₁ a₂| := by
        rw [abs_mul, abs_of_nonneg hM_nn, mul_comm (2 / 9 : ℝ) M_η]
        exact mul_le_mul_of_nonneg_left (pythRotMat_mg_sum_abs_ge' a₁ a₂) hM_nn
      have htri : |M_η * c_mg a₁ a₂| ≤
          |pythShellMap (k + 1) u_tilde.ofLp (.inr (e, (a₁, a₂)))| +
          |∑ pq : Fin 3 × Fin 3, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq| := by
        rw [hdecomp]
        simpa only [add_neg_cancel_right, abs_neg] using
          abs_add_le (M_η * c_mg a₁ a₂ + ∑ pq, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq)
            (-(∑ pq, pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * rem pq))
      dsimp [M_η] at hmain_abs
      linarith only [htri, hmain_abs, hrem_abs, le_abs_self η, abs_nonneg η]
  · intro e
    have hB_eq : bondMatrixOfPrefix (k + 1) (fun i => u (pathCoeffEquiv (k + 1) i)) e =
        pythRotMat * bondMatrix u_tilde e * pythRotMatᵀ := by
      ext p q
      simp only [bondMatrixOfPrefix, Equiv.apply_symm_apply]
      rw [show u (.inr (e, (p, q))) = pythShellMap (k + 1) u_tilde.ofLp (.inr (e, (p, q)))
        from congrFun hu_ofLp _]
      simp only [pythShellMap, Matrix.mul_apply, Matrix.transpose_apply, bondMatrix, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
    rw [hB_eq, bondMinorInvariant_orthog_eq _ pythRotMat pythRotMat pythRotMat_orthog'.1 pythRotMat_orthog'.1]
    obtain ⟨h00, h11⟩ := hbond_diag e
    have h01 := hbond_rem e (0, 1)
    have h10 := hbond_rem e (1, 0)
    simp only [one_ne_zero, zero_ne_one, and_false, false_and, or_self, ↓reduceIte, sub_zero] at h01 h10
    have hprod01 : |bondMatrix u_tilde e 0 1 * bondMatrix u_tilde e 1 0| ≤ 1 := by
      dsimp [bondMatrix]
      rw [abs_mul]
      exact (mul_le_mul h01 h10 (abs_nonneg _) (by norm_num)).trans (by norm_num)
    have hmin01 : |η| ^ 2 ≤
        bondMatrix u_tilde e 0 0 * bondMatrix u_tilde e 1 1 -
          bondMatrix u_tilde e 0 1 * bondMatrix u_tilde e 1 0 := by
      have hdiag_prod : M_η * M_η ≤ bondMatrix u_tilde e 0 0 * bondMatrix u_tilde e 1 1 :=
        mul_le_mul h00 h11 hM_nn (hM_nn.trans h00)
      have hoff_le : bondMatrix u_tilde e 0 1 * bondMatrix u_tilde e 1 0 ≤ 1 :=
        (le_abs_self _).trans hprod01
      dsimp [M_η] at hdiag_prod
      nlinarith only [hdiag_prod, hoff_le, abs_nonneg η]
    have hsingle : (bondMatrix u_tilde e 0 0 * bondMatrix u_tilde e 1 1 -
        bondMatrix u_tilde e 0 1 * bondMatrix u_tilde e 1 0) ^ 2 ≤
        bondMinorInvariant (bondMatrix u_tilde e) := by
      unfold bondMinorInvariant
      have hlt01 : (0 : Fin 3) < 1 := by decide
      have h1 := Finset.single_le_sum
        (f := fun q' : Fin 3 × Fin 3 => if (0 : Fin 3) < 1 ∧ q'.1 < q'.2 then
          (bondMatrix u_tilde e 0 q'.1 * bondMatrix u_tilde e 1 q'.2 -
            bondMatrix u_tilde e 0 q'.2 * bondMatrix u_tilde e 1 q'.1) ^ 2 else 0)
        (fun q' _ => by split_ifs <;> [exact sq_nonneg _; exact le_rfl])
        (Finset.mem_univ ((0 : Fin 3), (1 : Fin 3)))
      have h2 := Finset.single_le_sum
        (f := fun p' : Fin 3 × Fin 3 => ∑ q' : Fin 3 × Fin 3,
          if p'.1 < p'.2 ∧ q'.1 < q'.2 then
            (bondMatrix u_tilde e p'.1 q'.1 * bondMatrix u_tilde e p'.2 q'.2 -
              bondMatrix u_tilde e p'.1 q'.2 * bondMatrix u_tilde e p'.2 q'.1) ^ 2 else 0)
        (fun p' _ => Finset.sum_nonneg fun q' _ => by split_ifs <;> [exact sq_nonneg _; exact le_rfl])
        (Finset.mem_univ ((0 : Fin 3), (1 : Fin 3)))
      rw [if_pos ⟨hlt01, hlt01⟩] at h1
      exact h1.trans h2
    have hpow4 : η ^ 4 = (|η| ^ 2) ^ 2 := by rw [sq_abs]; ring
    rw [hpow4]
    exact (pow_le_pow_left₀ (sq_nonneg _) hmin01 2).trans hsingle
  · obtain ⟨hz, hx, hy⟩ := hsite 0
    rw [show u (.inl (0, 2)) = pythShellMap (k + 1) u_tilde.ofLp (.inl (0, 2))
      from congrFun hu_ofLp _]
    have hval_eq : pythShellMap (k + 1) u_tilde.ofLp (.inl (0, 2)) =
        (-2 / 3 : ℝ) * u_tilde (.inl (0, 0)) + (-2 / 3 : ℝ) * u_tilde (.inl (0, 1)) +
          (1 / 3 : ℝ) * u_tilde (.inl (0, 2)) := by
      simp [pythShellMap, Fin.sum_univ_three, pythRotMat]
    have hx2 := (abs_le.mp hx).2
    have hy2 := (abs_le.mp hy).2
    have hge : 3 ≤ pythShellMap (k + 1) u_tilde.ofLp (.inl (0, 2)) := by
      have h18 : 18 ≤ u_tilde (.inl (0, 2)) := hM_ge18.trans hz.1
      linarith only [hval_eq, hx2, hy2, h18, hδ_le]
    exact hge.trans (le_abs_self _)

private theorem hiddenMatchgate_onset_of_tilde_bounds (k : ℕ)
    (hentropy : atMostQuarterCircuitEntropyBound (k + 3)
      (nearHilbertContinuousCircuitBudget (k + 3)) < ((2 ^ (2 ^ (k + 3) - 1) : ℕ) : ℝ))
    (hP_ge : 2 * ((k + 3) * (2 * k + 5)) ≤ nearHilbertContinuousCircuitBudget (k + 3))
    (η T δ : ℝ) (hT2 : 2 ≤ T) (hδ_le_small : δ ≤ 1 / 200)
    (hδ_prod : T * (((7 * k + 16 : ℕ) : ℝ) * δ) ≤ 1 / 100)
    (u u_tilde : PathShell (k + 1)) (hu_ofLp : u.ofLp = pythShellMap (k + 1) u_tilde.ofLp)
    (hsite_in : ∀ v : Fin (k + 3),
      u_tilde (.inl (v, 2)) ∈ Icc (9 * |η| + 18) (9 * |η| + 18 + 1 / 20) ∧
      |u_tilde (.inl (v, 0))| ≤ δ ∧ |u_tilde (.inl (v, 1))| ≤ δ)
    (hbond_diag : ∀ e : Fin (k + 2),
      9 * |η| + 18 ≤ u_tilde (.inr (e, (0, 0))) ∧ 9 * |η| + 18 ≤ u_tilde (.inr (e, (1, 1))))
    (hbond_rem : ∀ (e : Fin (k + 2)) (pq : Fin 3 × Fin 3),
      |u_tilde (.inr (e, pq)) -
        (if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then 9 * |η| + 18 else 0)| ≤ 1 / 20)
    (hweak_le : ∀ l : PathLabel (k + 1), ¬ isMatchgateChainLabel l → |u_tilde l| ≤ δ)
    (hmax : MaximallyProjectiveEnergy
      (⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩ :
        selfAdjoint (Register (k + 3))).2.isHermitian.eigenvalues) :
    (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ allCoordStrongEvent (k + 1) η ∧
    (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ bondRankTwoEvent (k + 1) η ∧
    MaximallyProjectiveEnergy
      (⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩ :
        selfAdjoint (Register (k + 3))).2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ (k + 3)), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ (range fun m : Fin (2 ^ (k + 3)) =>
        unitaryEvolution (pathHamiltonian u) (((m : ℕ) : ℝ) * τ))) = 2 ^ (k + 3)) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution (pathHamiltonian u) t₀ - z • (1 : Register (k + 3))‖) ∧
    (∀ s : ℕ, (k + 3) * (2 * k + 5) ≤ s → s ≤ nearHilbertContinuousCircuitBudget (k + 3) →
      T < tenthPlateauOnset
        (⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩ : selfAdjoint (Register (k + 3))) s) := by
  have hT_pos : 0 < T := by linarith only [hT2]
  have hu_eq : u = WithLp.toLp 2 (pythShellMap (k + 1) u_tilde.ofLp) :=
    WithLp.ofLp_injective 2 hu_ofLp
  obtain ⟨hall_coord, hrank2, hz0_ge3⟩ :=
    pythTube_mem_strong_and_rankTwo k η δ hδ_le_small u u_tilde hu_ofLp hsite_in hbond_diag hbond_rem
  let H : selfAdjoint (Register (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  have hvand := vandermonde_full_rank_unit_interval H hmax.injective
  have hexc := exists_antipodal_return_excision_of_shell_coeff u (.inl (0, 2)) hz0_ge3 hT2
  let W_pyth : Register (k + 3) := prodLocalMatrix (fun _ : Fin (k + 3) => pythUnitary)
  have hW_unit : W_pyth ∈ unitary (Register (k + 3)) :=
    prodLocalMatrix_mem_unitary _ fun _ => pythUnitary_unitary'
  have hH_conj : W_pyth * pathHamiltonian u_tilde * star W_pyth = H.val := by
    change W_pyth * pathHamiltonian u_tilde * star W_pyth = pathHamiltonian u
    rw [prodPyth_conj_pathHamiltonian' u_tilde, ← hu_eq]
  have hev_conj (t : ℝ) :
      unitaryEvolution H.val t = W_pyth * unitaryEvolution (pathHamiltonian u_tilde) t * star W_pyth := by
    let W_ug : Matrix.unitaryGroup (Config (k + 3)) ℂ := ⟨W_pyth, hW_unit⟩
    have hc := unitaryEvolution_conj W_pyth (pathHamiltonian u_tilde) (Unitary.isUnit_coe (U := W_ug)) t
    rw [inv_eq_star_of_mem_unitary hW_unit, hH_conj] at hc
    exact hc
  let S_mg : Finset (PathLabel (k + 1)) := Finset.univ.filter isMatchgateChainLabel
  let S_weak : Finset (PathLabel (k + 1)) := Finset.univ \ S_mg
  have hcard_weak : S_weak.card = 7 * k + 16 := by
    have hcard_mg : S_mg.card = 5 * k + 11 := card_filter_matchgateChainLabel k
    have hcard_tot : Fintype.card (PathLabel (k + 1)) = 12 * k + 27 := by
      simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S_mg)
    rw [Finset.card_univ, hcard_tot, hcard_mg] at h1; dsimp only [S_weak]; omega
  let u_tilde_mg : PathShell (k + 1) :=
    WithLp.toLp 2 fun l => if isMatchgateChainLabel l then u_tilde l else 0
  have htilde_mg_off : ∀ l : PathLabel (k + 1), ¬ isMatchgateChainLabel l → u_tilde_mg l = 0 :=
    fun l hl => if_neg hl
  have hdiff_tilde : ‖pathHamiltonian u_tilde - pathHamiltonian u_tilde_mg‖ ≤
      ((7 * k + 16 : ℕ) : ℝ) * δ := by
    have hdis_mw : Disjoint S_mg S_weak := disjoint_sdiff_self_right
    have hun_mw : S_mg ∪ S_weak = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hsub_sum : pathHamiltonian u_tilde - pathHamiltonian u_tilde_mg =
        ∑ l ∈ S_weak, ((u_tilde l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) := by
      rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, ← Finset.sum_sub_distrib,
        ← hun_mw, Finset.sum_union hdis_mw]
      have hmg0 : (∑ l ∈ S_mg, (((u_tilde l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) -
          ((u_tilde_mg l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))) = 0 :=
        Finset.sum_eq_zero fun l hl => by
          rw [show u_tilde_mg l = u_tilde l from if_pos (Finset.mem_filter.mp hl).2, sub_self]
      rw [hmg0, zero_add]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hnot : ¬ isMatchgateChainLabel l := fun h => (Finset.mem_sdiff.mp hl).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
      rw [show u_tilde_mg l = 0 from if_neg hnot, Complex.ofReal_zero, zero_smul, sub_zero]
    rw [hsub_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm (l : PathLabel (k + 1)) (hl : l ∈ S_weak) :
        ‖((u_tilde l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)‖ ≤ δ := by
      rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hweak_le l (fun h => (Finset.mem_sdiff.mp hl).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩))
    calc ∑ l ∈ S_weak, ‖((u_tilde l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)‖
        ≤ ∑ _l ∈ S_weak, δ := Finset.sum_le_sum hterm
      _ = ((7 * k + 16 : ℕ) : ℝ) * δ := by rw [Finset.sum_const, hcard_weak, nsmul_eq_mul]
  have hearly_inc (t : ℝ) (ht : |t| ≤ T) :
      HasProjectiveCircuitApproximation (k + 3) (1 / 100 : ℝ) ((k + 3) * (2 * k + 5))
        (unitaryEvolution H.val t) := by
    have hreal_rot := realizes_conj_prodLocalMatrix (fun _ : Fin (k + 3) => pythUnitary)
      (fun _ => pythUnitary_unitary')
      (realizes_choose_twoN_of_matchgateChain u_tilde_mg htilde_mg_off t)
    have hs_eq : (k + 1 + 2) * (2 * (k + 1) + 3) = (k + 3) * (2 * k + 5) := by ring
    rw [hs_eq] at hreal_rot
    obtain ⟨z, hz, C, hC, hU_rot⟩ := hreal_rot
    refine ⟨z, hz, C, hC, ?_⟩
    change ‖unitaryEvolution H.val t - z • C.eval.val‖ ≤ _
    rw [← hU_rot, hev_conj t]
    change ‖W_pyth * unitaryEvolution (pathHamiltonian u_tilde) t * star W_pyth -
      W_pyth * unitaryEvolution (pathHamiltonian u_tilde_mg) t * star W_pyth‖ ≤ _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, l2_opNorm_unitary_conj_eq (V := W_pyth) hW_unit]
    exact ((norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u_tilde)
      (isSelfAdjoint_pathHamiltonian u_tilde_mg) t).trans
      (mul_le_mul ht hdiff_tilde (norm_nonneg _) hT_pos.le)).trans hδ_prod
  let d := 2 ^ (k + 3) - 1
  let e_fin : Config (k + 3) ≃ Fin (d + 1) := (Fintype.equivFin _).trans
    (finCongr (by
      simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      have hd : 0 < 2 ^ (k + 3) := Nat.two_pow_pos (k + 3)
      dsimp [d]; omega))
  obtain ⟨σ, hσ_gt, hσ_eq, _, _, _⟩ := first_circuit_threshold_of_increment e_fin H
    (hmax.comp_equiv e_fin.symm) hentropy T hT_pos.le hP_ge hearly_inc
  refine ⟨hall_coord, hrank2, hmax, hvand, hexc, fun s hs_lo hs_hi => ?_⟩
  have hearly (t : ℝ) (ht : t ∈ Icc 0 T) : orbitCircuitDistance H s t < 1 / 10 := by
    have habs : |t| ≤ T := by rw [abs_of_nonneg ht.1]; exact ht.2
    obtain ⟨z, hz, C, hC, herr⟩ := hearly_inc t habs
    have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 100 : ℝ)).mp
      ⟨z, hz, C, hC.trans hs_lo, herr⟩
    change orbitCircuitDistance H s t ≤ 1 / 100 at hd
    linarith only [hd]
  have hB_gt : 1 / 10 < orbitCircuitDistance H s σ := by
    have hmono : orbitCircuitDistance H (nearHilbertContinuousCircuitBudget (k + 3)) σ ≤
        orbitCircuitDistance H s σ := by
      apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
        (le_rfl : orbitCircuitDistance H s σ ≤ _)
      exact ⟨z, hz, C, hC.trans hs_hi, herr⟩
    rw [hσ_eq] at hmono
    linarith only [hmono]
  exact (tenthPlateauOnset_spec H hT_pos (hT_pos.trans hσ_gt).le hearly hB_gt).1

/-- Hidden locally rotated matchgate survival tube **strictly inside
`allCoordStrongEvent (k + 1) η ∩ bondRankTwoEvent (k + 1) η`**: for every `η : ℝ` and all
sufficiently large `k` (`N = k + 3`), there is `c > 0` such that for every `T ≥ 2`, an event of
`pathPauliDisorderLaw` probability `≥ c * T ^ -(7 * k + 16)` simultaneously satisfies:
1. `x ∈ allCoordStrongEvent (k + 1) η` and `x ∈ bondRankTwoEvent (k + 1) η`,
2. maximally projective simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2`
   scalar-return excision, yet
3. `T < tenthPlateauOnset H s` for **every** budget `(k + 3) * (2 * k + 5) ≤ s ≤ P`
   (`choose(2N, 2) ≤ s ≤ P`). -/
theorem gaussian_hiddenMatchgate_rankTwo_tube_tail (η : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
        c ≤ T ^ (7 * k + 16) * pathPauliDisorderLaw.real {ω : PathPauliDisorder |
          let u := pathPauliDisorderShell ω (k + 1)
          let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          x ∈ allCoordStrongEvent (k + 1) η ∧
          x ∈ bondRankTwoEvent (k + 1) η ∧
          MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
          (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
            Module.finrank ℂ (Submodule.span ℂ
              (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
          (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
            Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
          (∀ s : ℕ, (k + 3) * (2 * k + 5) ≤ s → s ≤ P → T < tenthPlateauOnset H s)} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let γ := gaussianReal 0 1
  have hent := (tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent, eventually_ge_atTop 22] with k hentropy hklarge
  intro N P
  let s_mg : ℕ := (k + 3) * (2 * k + 5)
  have hP_ge : 2 * s_mg ≤ P := by
    dsimp only [P, N, s_mg, nearHilbertContinuousCircuitBudget]
    have hind : ∀ m : ℕ, 22 ≤ m → 64 * (m + 4) * (2 * ((m + 3) * (2 * m + 5))) ≤ 2 ^ (m + 3) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
          have hstep : 64 * (m + 5) * (2 * ((m + 4) * (2 * m + 7))) ≤
              2 * (64 * (m + 4) * (2 * ((m + 3) * (2 * m + 5)))) := by
            have hq : (m + 5) * (2 * m + 7) ≤ 2 * (m + 3) * (2 * m + 5) := by nlinarith only [hm]
            calc 64 * (m + 5) * (2 * ((m + 4) * (2 * m + 7)))
                = (128 * (m + 4)) * ((m + 5) * (2 * m + 7)) := by ring
              _ ≤ (128 * (m + 4)) * (2 * (m + 3) * (2 * m + 5)) := Nat.mul_le_mul_left _ hq
              _ = 2 * (64 * (m + 4) * (2 * ((m + 3) * (2 * m + 5)))) := by ring
          exact hstep.trans ((Nat.mul_le_mul_left 2 ih).trans_eq (pow_succ' 2 (m + 3)).symm)
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hind k hklarge)
  let M_η : ℝ := 9 * |η| + 18
  have hM_ge18 : 18 ≤ M_η := by
    have hnn : 0 ≤ |η| := abs_nonneg η
    dsimp [M_η]; linarith only [hnn]
  have hM_ge_eta : 9 * |η| + 18 ≤ M_η := le_rfl
  let S_mg : Finset (PathLabel (k + 1)) := Finset.univ.filter isMatchgateChainLabel
  let S_strong : Finset (PathLabel (k + 1)) := Finset.univ.filter isStrongMatchgateLabel
  let S_xy : Finset (PathLabel (k + 1)) := S_mg \ S_strong
  let S_weak : Finset (PathLabel (k + 1)) := Finset.univ \ S_mg
  have hstrong_sub : S_strong ⊆ S_mg := by
    intro l hl
    have hs := (Finset.mem_filter.mp hl).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩
    rcases l with ⟨v, a⟩ | ⟨e, ⟨p, q⟩⟩
    · exact hs
    · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [isMatchgateChainLabel]
  have hcard_mg : S_mg.card = 5 * k + 11 := card_filter_matchgateChainLabel k
  have hcard_strong : S_strong.card = 3 * k + 7 := card_filter_strongMatchgateLabel k
  have hcard_xy : S_xy.card = 2 * k + 4 := by
    have h1 := Finset.card_sdiff_add_card_eq_card hstrong_sub
    rw [hcard_mg, hcard_strong] at h1; dsimp only [S_xy]; omega
  have hcard_tot : Fintype.card (PathLabel (k + 1)) = 12 * k + 27 := by
    simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  have hcard_weak : S_weak.card = 7 * k + 16 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S_mg)
    rw [Finset.card_univ, hcard_tot, hcard_mg] at h1; dsimp only [S_weak]; omega
  have hp_strong : 0 < γ.real (Icc M_η (M_η + 1 / 20)) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by linarith)).ne' (measure_ne_top _ _)
  have hp_xy : 0 < γ.real (Icc (0 : ℝ) (1 / 20)) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num)).ne' (measure_ne_top _ _)
  let W_num : ℝ := 100 * ((7 * k + 16 : ℕ) : ℝ)
  have hW_pos : 0 < W_num := by dsimp only [W_num]; positivity
  let c : ℝ := (γ.real (Icc M_η (M_η + 1 / 20))) ^ (3 * k + 7) *
    (γ.real (Icc (0 : ℝ) (1 / 20))) ^ (2 * k + 4) *
    (2 * gaussianDensityFloor / W_num) ^ (7 * k + 16)
  have hc_pos : 0 < c :=
    mul_pos (mul_pos (pow_pos hp_strong _) (pow_pos hp_xy _))
      (pow_pos (div_pos (mul_pos two_pos gaussianDensityFloor_pos) hW_pos) _)
  refine ⟨c, hc_pos, fun T hT2 => ?_⟩
  have hT_pos : 0 < T := by linarith only [hT2]
  let δ : ℝ := 1 / (W_num * T)
  have hδ_pos : 0 < δ := div_pos zero_lt_one (mul_pos hW_pos hT_pos)
  have hδ_le_small : δ ≤ 1 / 200 := by
    have hW100 : 100 ≤ W_num := by
      dsimp only [W_num]
      have : (1 : ℝ) ≤ ((7 * k + 16 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 7 * k + 16 by omega)
      linarith only [this]
    rw [div_le_div_iff₀ (mul_pos hW_pos hT_pos) (by norm_num)]
    nlinarith only [hW100, hT2]
  let F_coord : PathLabel (k + 1) → Set ℝ := fun l =>
    if l ∈ S_strong then Icc M_η (M_η + 1 / 20)
    else if l ∈ S_mg then Icc (0 : ℝ) (1 / 20)
    else Icc (-δ) δ
  let MGBox : Set (PathLabel (k + 1) → ℝ) := Set.univ.pi F_coord
  have hMGBox_meas : MeasurableSet MGBox :=
    MeasurableSet.pi (Set.to_countable _) fun l _ => by
      dsimp only [F_coord]; split_ifs <;> exact measurableSet_Icc
  have hMGBox_mass : (γ.real (Icc M_η (M_η + 1 / 20))) ^ (3 * k + 7) *
      (γ.real (Icc (0 : ℝ) (1 / 20))) ^ (2 * k + 4) *
      (2 * gaussianDensityFloor * δ) ^ (7 * k + 16) ≤
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real MGBox := by
    have hdis1 : Disjoint S_strong S_xy := disjoint_sdiff_self_right
    have hun_mg : S_strong ∪ S_xy = S_mg := Finset.union_sdiff_of_subset hstrong_sub
    have hdis2 : Disjoint S_mg S_weak := disjoint_sdiff_self_right
    have hun_all : S_mg ∪ S_weak = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hprod_eq : (Measure.pi fun _ : PathLabel (k + 1) => γ).real MGBox =
        (∏ l ∈ S_strong, γ.real (F_coord l)) * (∏ l ∈ S_xy, γ.real (F_coord l)) *
          (∏ l ∈ S_weak, γ.real (F_coord l)) := by
      rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod, ← hun_all,
        Finset.prod_union hdis2, ← hun_mg, Finset.prod_union hdis1]; rfl
    have hps : (∏ l ∈ S_strong, γ.real (F_coord l)) =
        (γ.real (Icc M_η (M_η + 1 / 20))) ^ (3 * k + 7) := by
      have h1 : ∀ l ∈ S_strong, F_coord l = Icc M_η (M_η + 1 / 20) := fun _ hl => if_pos hl
      rw [Finset.prod_congr rfl fun l hl => by rw [h1 l hl], Finset.prod_const, hcard_strong]
    have hpx : (∏ l ∈ S_xy, γ.real (F_coord l)) =
        (γ.real (Icc (0 : ℝ) (1 / 20))) ^ (2 * k + 4) := by
      have h1 : ∀ l ∈ S_xy, F_coord l = Icc (0 : ℝ) (1 / 20) := fun l hl => by
        obtain ⟨hmg, hns⟩ := Finset.mem_sdiff.mp hl
        simp [F_coord, hns, hmg]
      rw [Finset.prod_congr rfl fun l hl => by rw [h1 l hl], Finset.prod_const, hcard_xy]
    have hpw : (∏ l ∈ S_weak, γ.real (F_coord l)) = (γ.real (Icc (-δ) δ)) ^ (7 * k + 16) := by
      have h1 : ∀ l ∈ S_weak, F_coord l = Icc (-δ) δ := fun l hl => by
        have hnmg : l ∉ S_mg := (Finset.mem_sdiff.mp hl).2
        have hns : l ∉ S_strong := fun hs => hnmg (hstrong_sub hs)
        simp [F_coord, hns, hnmg]
      rw [Finset.prod_congr rfl fun l hl => by rw [h1 l hl], Finset.prod_const, hcard_weak]
    have hlow_enn := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ))
      (gaussianReal_Icc_lower (hδ_le_small.trans (by norm_num)))
    rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hδ_pos])),
      ← Measure.real_def] at hlow_enn
    have h1d : 2 * gaussianDensityFloor * δ ≤ γ.real (Icc (-δ) δ) := by linarith only [hlow_enn]
    rw [hprod_eq, hps, hpx, hpw]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg two_pos.le gaussianDensityFloor_pos.le) hδ_pos.le) h1d _)
      (mul_nonneg (pow_nonneg measureReal_nonneg _) (pow_nonneg measureReal_nonneg _))
  let PhysTube : Set (PathLabel (k + 1) → ℝ) := pythShellInv (k + 1) ⁻¹' MGBox
  have hPhysTube_meas : MeasurableSet PhysTube := by
    have hm_inv : Measurable (pythShellInv (k + 1)) := by
      refine measurable_pi_lambda _ fun l => ?_
      rcases l with ⟨v, b⟩ | ⟨e, ⟨b₁, b₂⟩⟩
      · exact Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_pi_apply _)
      · exact Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
          measurable_const.mul (measurable_pi_apply _)
    exact hMGBox_meas.preimage hm_inv
  have hPhysTube_mass : (Measure.pi fun _ : PathLabel (k + 1) => γ).real PhysTube =
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real MGBox := by
    have hpre := (pythShellMap_measurePreserving' (k + 1)).measure_preimage
      hPhysTube_meas.nullMeasurableSet
    have heq_set : pythShellMap (k + 1) ⁻¹' PhysTube = MGBox := by
      ext z; change pythShellInv (k + 1) (pythShellMap (k + 1) z) ∈ MGBox ↔ z ∈ MGBox
      rw [pythShellInv_left']
    rw [heq_set] at hpre
    exact (congrArg ENNReal.toReal hpre).symm
  let u_map : PathPauliDisorder → PathLabel (k + 1) → ℝ :=
    fun ω l => pathPauliDisorderShell ω (k + 1) l
  have hpre_mass : pathPauliDisorderLaw.real (u_map ⁻¹' PhysTube) =
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real MGBox :=
    (congrArg ENNReal.toReal
      ((measurePreserving_pathDisorder_labels (k + 1)).measure_preimage
        hPhysTube_meas.nullMeasurableSet)).trans hPhysTube_mass
  let TargetEvent : Set PathPauliDisorder := {ω : PathPauliDisorder |
    let u := pathPauliDisorderShell ω (k + 1)
    let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    x ∈ allCoordStrongEvent (k + 1) η ∧
    x ∈ bondRankTwoEvent (k + 1) η ∧
    MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
    (∀ s : ℕ, s_mg ≤ s → s ≤ P → T < tenthPlateauOnset H s)}
  have hae_sub : u_map ⁻¹' PhysTube ≤ᵐ[pathPauliDisorderLaw] TargetEvent := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hmax_all hω_in
    let u := pathPauliDisorderShell ω (k + 1)
    let u_tilde : PathShell (k + 1) := WithLp.toLp 2 (pythShellInv (k + 1) u.ofLp)
    have hu_ofLp : u.ofLp = pythShellMap (k + 1) u_tilde.ofLp :=
      (pythShellInv_right' (k + 1) u.ofLp).symm
    have htilde_box : ∀ l : PathLabel (k + 1), u_tilde l ∈ F_coord l := fun l =>
      hω_in l (mem_univ l)
    have hsite_in (v : Fin (k + 3)) :
        u_tilde (.inl (v, 2)) ∈ Icc M_η (M_η + 1 / 20) ∧
        |u_tilde (.inl (v, 0))| ≤ δ ∧ |u_tilde (.inl (v, 1))| ≤ δ := by
      have hz := htilde_box (.inl (v, 2))
      have hx := htilde_box (.inl (v, 0))
      have hy := htilde_box (.inl (v, 1))
      have hz_s : Sum.inl (v, (2 : Fin 3)) ∈ S_strong := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hx_ns : Sum.inl (v, (0 : Fin 3)) ∉ S_strong := by simp [S_strong, isStrongMatchgateLabel]
      have hx_nmg : Sum.inl (v, (0 : Fin 3)) ∉ S_mg := by simp [S_mg, isMatchgateChainLabel]
      have hy_ns : Sum.inl (v, (1 : Fin 3)) ∉ S_strong := by simp [S_strong, isStrongMatchgateLabel]
      have hy_nmg : Sum.inl (v, (1 : Fin 3)) ∉ S_mg := by simp [S_mg, isMatchgateChainLabel]
      exact ⟨by simpa [F_coord, hz_s] using hz,
        abs_le.mpr (by simpa [F_coord, hx_ns, hx_nmg] using hx),
        abs_le.mpr (by simpa [F_coord, hy_ns, hy_nmg] using hy)⟩
    have hbond_diag (e : Fin (k + 2)) :
        M_η ≤ u_tilde (.inr (e, (0, 0))) ∧ M_η ≤ u_tilde (.inr (e, (1, 1))) := by
      have h00_mem : Sum.inr (e, ((0 : Fin 3), (0 : Fin 3))) ∈ S_strong :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
      have h11_mem : Sum.inr (e, ((1 : Fin 3), (1 : Fin 3))) ∈ S_strong :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
      have h00 : u_tilde (.inr (e, (0, 0))) ∈ Icc M_η (M_η + 1 / 20) := by
        simpa [F_coord, h00_mem] using htilde_box (.inr (e, (0, 0)))
      have h11 : u_tilde (.inr (e, (1, 1))) ∈ Icc M_η (M_η + 1 / 20) := by
        simpa [F_coord, h11_mem] using htilde_box (.inr (e, (1, 1)))
      exact ⟨h00.1, h11.1⟩
    have hbond_rem (e : Fin (k + 2)) (pq : Fin 3 × Fin 3) :
        |u_tilde (.inr (e, pq)) -
          (if (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1) then M_η else 0)| ≤ 1 / 20 := by
      have hb := htilde_box (.inr (e, pq))
      by_cases hs : (pq.1 = 0 ∧ pq.2 = 0) ∨ (pq.1 = 1 ∧ pq.2 = 1)
      · have hmem : Sum.inr (e, pq) ∈ S_strong := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
        simp only [F_coord, if_pos hmem, mem_Icc] at hb
        rw [if_pos hs, abs_le]; constructor <;> linarith only [hb.1, hb.2]
      · have hnmem : Sum.inr (e, pq) ∉ S_strong := fun h => hs (Finset.mem_filter.mp h).2
        rw [if_neg hs, sub_zero]
        by_cases hmg : Sum.inr (e, pq) ∈ S_mg
        · simp only [F_coord, if_neg hnmem, if_pos hmg, mem_Icc] at hb
          rw [abs_le]; constructor <;> linarith only [hb.1, hb.2]
        · simp only [F_coord, if_neg hnmem, if_neg hmg, mem_Icc] at hb
          rw [abs_le]; constructor <;> linarith only [hb.1, hb.2, hδ_le_small]
    have hweak_le (l : PathLabel (k + 1)) (hl : ¬ isMatchgateChainLabel l) : |u_tilde l| ≤ δ := by
      have hnmg : l ∉ S_mg := fun h => hl (Finset.mem_filter.mp h).2
      have hns : l ∉ S_strong := fun hs => hnmg (hstrong_sub hs)
      exact abs_le.mpr (by simpa only [F_coord, if_neg hns, if_neg hnmg, mem_Icc] using htilde_box l)
    have hδ_prod : T * (((7 * k + 16 : ℕ) : ℝ) * δ) ≤ 1 / 100 := by
      have hWT_ne : W_num * T ≠ 0 := mul_ne_zero hW_pos.ne' hT_pos.ne'
      refine le_of_eq (mul_right_cancel₀ hWT_ne ?_)
      calc T * (((7 * k + 16 : ℕ) : ℝ) * δ) * (W_num * T)
          = T * ((7 * k + 16 : ℕ) : ℝ) * (δ * (W_num * T)) := by ring
        _ = T * ((7 * k + 16 : ℕ) : ℝ) * 1 := by dsimp only [δ]; rw [one_div_mul_cancel hWT_ne]
        _ = 1 / 100 * (W_num * T) := by dsimp only [W_num]; ring
    exact hiddenMatchgate_onset_of_tilde_bounds k hentropy hP_ge η T δ hT2 hδ_le_small hδ_prod
      u u_tilde hu_ofLp hsite_in hbond_diag hbond_rem hweak_le (hmax_all k)
  have hmeas_le : (Measure.pi fun _ : PathLabel (k + 1) => γ).real MGBox ≤
      pathPauliDisorderLaw.real TargetEvent := by
    rw [← hpre_mass]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae_sub)
  have hc_eq : c = T ^ (7 * k + 16) *
      ((γ.real (Icc M_η (M_η + 1 / 20))) ^ (3 * k + 7) *
        (γ.real (Icc (0 : ℝ) (1 / 20))) ^ (2 * k + 4) *
        (2 * gaussianDensityFloor * δ) ^ (7 * k + 16)) := by
    dsimp only [c, δ]
    have hpow_T : T ^ (7 * k + 16) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (7 * k + 16) =
        (2 * gaussianDensityFloor / W_num) ^ (7 * k + 16) := by
      rw [← mul_pow]; congr 1
      have hWT_ne : W_num * T ≠ 0 := mul_ne_zero hW_pos.ne' hT_pos.ne'
      refine mul_right_cancel₀ hWT_ne ?_
      calc T * (2 * gaussianDensityFloor * (1 / (W_num * T))) * (W_num * T)
          = T * (2 * gaussianDensityFloor) * ((1 / (W_num * T)) * (W_num * T)) := by ring
        _ = T * (2 * gaussianDensityFloor) * 1 := by rw [one_div_mul_cancel hWT_ne]
        _ = ((2 * gaussianDensityFloor / W_num) * W_num) * T := by
              rw [div_mul_cancel₀ _ hW_pos.ne']; ring
        _ = 2 * gaussianDensityFloor / W_num * (W_num * T) := by ring
    calc c = (γ.real (Icc M_η (M_η + 1 / 20))) ^ (3 * k + 7) *
            (γ.real (Icc (0 : ℝ) (1 / 20))) ^ (2 * k + 4) *
            (T ^ (7 * k + 16) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (7 * k + 16)) := by
              dsimp only [c]; rw [hpow_T]
      _ = _ := by ring
  rw [hc_eq]
  exact mul_le_mul_of_nonneg_left (hMGBox_mass.trans hmeas_le) (pow_nonneg hT_pos.le _)

#print axioms realizes_choose_twoN_of_matchgateChain
#print axioms realizes_conj_prodLocalMatrix
#print axioms realizes_choose_twoN_of_locallyRotatedMatchgate
#print axioms gaussian_hiddenMatchgate_rankTwo_tube_tail

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
