/-
Finite reflection brackets adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.PrimaryCuspCompletions

/-!
# Finite reflection brackets

Cubic reflection of an active prime set produces explicit characters and divisibility
brackets `finiteReflectionBracket`; the exceptional fourth power becomes a bracket. Divisor
series, periodic arrays and the full bounds on the source cusp coefficients.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap

/-- The smoothed reflection of an active prime set uses only constructed arithmetic data. -/
theorem exists_native_smoothed_cusp_reflection {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp0 : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpair : Pairwise (Function.onFun IsCoprime p)) (hp : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N a c : O) (hc : c ≠ 0) (hN : (27 : O) * c ∣ N)
    (hNp : ∀ i, IsCoprime N (p i)) (hac : IsCoprime a c) (mode : Bool)
    (hbase : if mode then lambda ^ 2 ∣ a - 1 else lambda ^ 2 ∣ c - 1) :
    ∃ (lift : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → ι → O)
      (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O))
      (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (U : O) (κ : ℂ),
      (∀ v i, N ^ 2 ∣ lift v i) ∧
      (∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = (v i : O ⧸ Ideal.span {p i})) ∧
      (∀ v, M v 0 0 = cuspCrossNumerator a c traceLambda p (lift v)) ∧
      (∀ v, M v 1 0 = c * ∏ i, p i) ∧
      (∀ v r s, N ∣ M v r s - M (fun _ => 1) r s) ∧
      ‖κ‖ = 1 ∧ ∀ (j : ι → ℕ) (V : ℝ → ℂ) (A B : ℝ), 0 < A →
        Function.support V ⊆ Set.Icc A B → ContDiff ℝ ∞ V → ∀ X : ℝ, 0 < X →
        cuspUnitSourceSum p hp0 hg c M j V X =
          nativeCuspStratumKernel p hp0 hg (fixedCuspSector (M (fun _ => 1))) c
            (M (fun _ => 1) 1 1) U κ σ ε j V X := by
  obtain ⟨lift, M, σ, ε, U, κ, hperiod, hres, hMa, hMc, hfixed, hκ, hreflect⟩ :=
    exists_native_cusp_reflection p hp0 hg hpair hp N a c hc hN hNp hac mode hbase
  have h3N : (3 : O) ∣ N := (show (3 : O) ∣ 27 * c from ⟨9 * c, by ring⟩).trans hN
  have hsector (v) : fixedCuspSector (M v) = fixedCuspSector (M (fun _ => 1)) := by
    apply fixedCuspSector_eq_of_relative
    exact integralMatrix_congruent_levelThree (M v) (M (fun _ => 1))
      (fun i j => h3N.trans (hfixed v i j))
  refine ⟨lift, M, σ, ε, U, κ, hperiod, hres, hMa, hMc, hfixed, hκ, ?_⟩
  intro j V A B hA hs hV X hX
  rw [cuspUnitSourceSum_reflection p hp0 hg c hc M _ hsector hMc j V A B hA hs hV X hX]
  simp_rw [hreflect j]
  rfl

/-- The exponent of the character produced by cubic reflection. -/
def reflectedSexticExponent (j : ℕ) : ℕ := (10 - j) % 6

lemma inverse_reflectedSexticExponent {F : Type*} [CommGroup F] (χ : F) (hχ : χ ^ 6 = 1)
    (j : ℕ) (hj : j < 6) : (χ ^ (j + 2))⁻¹ = χ ^ reflectedSexticExponent j := by
  have hd : 6 ∣ j + 2 + reflectedSexticExponent j := by
    interval_cases j <;> norm_num [reflectedSexticExponent]
  obtain ⟨n, hn⟩ := hd
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, hn, pow_mul, hχ, one_pow]

/-- The exceptional fourth power becomes a divisibility bracket; all other powers remain characters. -/
def finiteReflectionBracket {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then (if x = 0 then (Fintype.card F : ℂ) else 0) - 1
  else (χ ^ reflectedSexticExponent j) x

/-- Canonical local reflection, with its exact squared normalization. -/
theorem finiteReflectionGauss_actual_bracket (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (if j = 0 ∨ j = 4 then (Fintype.card (O ⧸ P) : ℝ)⁻¹ else 1) ∧
      ∀ x, finiteReflectionGauss (complexSexticChar P hg) ψ j x =
        β * finiteReflectionBracket (complexSexticChar P hg) j x := by
  classical
  let χ := complexSexticChar P hg
  have h6 : χ ^ 6 = 1 := (complexSexticChar_powers P hg).2.2
  by_cases hj4 : j = 4
  · subst j
    have h4 : χ ^ 4 ≠ 1 := complexSexticChar_pow_ne_one P hg hchar 4 (by decide) (by decide)
    refine ⟨(Fintype.card (O ⧸ P) : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1)), ?_, ?_⟩
    · rw [if_pos (Or.inr rfl)]
      exact finiteReflectionGauss_fourth_phase_norm_sq χ ψ hψ h4
    · intro x
      simpa only [finiteReflectionBracket, reduceIte] using finiteReflectionGauss_fourth_indicator χ ψ h6 hψ x
  · have hexp : reflectedSexticExponent j < 6 := Nat.mod_lt _ (by decide)
    have hexp0 : reflectedSexticExponent j ≠ 0 := by
      unfold reflectedSexticExponent
      omega
    have hinv := inverse_reflectedSexticExponent χ h6 j hj
    have hnext : χ ^ (j + 2) ≠ 1 := by
      intro he
      apply complexSexticChar_pow_ne_one P hg hchar _ hexp hexp0
      rw [← hinv, he, inv_one]
    refine ⟨(Fintype.card (O ⧸ P) : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) * gaussSum (χ ^ (j + 2)) ψ, ?_, ?_⟩
    · by_cases hj0 : j = 0
      · subst j
        rw [if_pos (Or.inl rfl)]
        simpa only [pow_zero, zero_add] using finiteReflectionGauss_trivial_phase_norm_sq χ ψ hψ hnext
      · rw [finiteReflectionGauss_phase_norm χ ψ hψ j
          (complexSexticChar_pow_ne_one P hg hchar j hj hj0) hnext,
          one_pow, if_neg (not_or.mpr ⟨hj0, hj4⟩)]
    · intro x
      rw [finiteReflectionGauss_nonexceptional χ ψ j hnext, hinv,
        finiteReflectionBracket, if_neg hj4]

/-- Scaling the reflected frequency by a unit changes only a constant phase. -/
def finiteReflectionUnitFactor {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) : ℂ :=
  if j = 4 then 1 else (χ ^ reflectedSexticExponent j) u

lemma finiteReflectionUnitFactor_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) : ‖finiteReflectionUnitFactor χ j u‖ = 1 := by
  by_cases hj : j = 4
  · simp only [finiteReflectionUnitFactor, if_pos hj, norm_one]
  · simp only [finiteReflectionUnitFactor, if_neg hj, finiteMulChar_unit_norm]

lemma finiteReflectionBracket_unit_mul {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) (x : F) :
    finiteReflectionBracket χ j ((u : F) * x) =
      finiteReflectionUnitFactor χ j u * finiteReflectionBracket χ j x := by
  by_cases hj : j = 4
  · simp only [finiteReflectionBracket, finiteReflectionUnitFactor, if_pos hj, mul_eq_zero, u.ne_zero,
      false_or, one_mul]
  · simp only [finiteReflectionBracket, finiteReflectionUnitFactor, if_neg hj, map_mul]

/-- After extracting one row phase, the full reflection consists of explicit characters and divisor brackets. -/
theorem finiteReflectionGauss_bracket_family
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (σ ε : ∀ i, (O ⧸ P i)ˣ) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then (Fintype.card (O ⧸ P i) : ℝ)⁻¹ else 1) ∧
      ∀ x : ∀ i, O ⧸ P i,
      (∏ i, ((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (σ i) *
        finiteReflectionGauss (complexSexticChar (P i) (hg i)) (ψ i) (j i) ((ε i : O ⧸ P i) * x i)) =
      β * ∏ i, finiteReflectionBracket (complexSexticChar (P i) (hg i)) (j i) (x i) := by
  classical
  choose β hβnorm hβ using fun i => finiteReflectionGauss_actual_bracket
    (P i) (hg i) (hchar i) (ψ i) (hψ i) (j i) (hj i)
  refine ⟨∏ i, (((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (σ i) * β i *
    finiteReflectionUnitFactor (complexSexticChar (P i) (hg i)) (j i) (ε i)), ?_, ?_⟩
  · simp only [norm_prod, norm_mul, finiteMulChar_unit_norm, finiteReflectionUnitFactor_norm, one_mul, mul_one]
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => hβnorm i)
  · intro x
    simp_rw [hβ, finiteReflectionBracket_unit_mul]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)

/-- The completed row has an exact active-prime reflection with every cusp, matrix, and local phase constructed. -/
theorem completedT_constructed_active_reflection {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp0 : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hp : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (N c : O) (hc : c ≠ 0) (hN : (243 : O) * c ∣ N) (hNp : ∀ i, IsCoprime N (p i))
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) (j : ι → ℕ) :
    ∃ (c₀ : (O ⧸ Ideal.span {9 * c}) → O)
      (sector : (O ⧸ Ideal.span {9 * c}) → Finset ι → FixedCuspSector)
      (d U : (O ⧸ Ideal.span {9 * c}) → Finset ι → O)
      (κ : (O ⧸ Ideal.span {9 * c}) → Finset ι → ℂ)
      (σ ε : ∀ k : O ⧸ Ideal.span {9 * c}, ∀ s : Finset ι, ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ),
      (∀ k, c₀ k ≠ 0 ∧ c₀ k ∣ 9 * c) ∧ (∀ k s, ‖κ k s‖ = 1) ∧
      ∀ (W : ℝ → ℂ) (A B : ℝ), 0 < A → Function.support W ⊆ Set.Icc A B →
        ContDiff ℝ ∞ W → ∀ X : ℝ, 0 < X →
        completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom *
          primeCuspRowCharacter p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)) W X =
        thetaDerivativeScalar⁻¹ * ∑ k : O ⧸ Ideal.span {9 * c},
          finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
            (finiteThetaTwist c Ψ) k *
          ∑ s : Finset ι,
            (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp0 i.val))
              (complexSexticChar (Ideal.span {p i.val}) (hg i.val) ^ j i.val : MulChar (O ⧸ Ideal.span {p i.val}) ℂ) 0) *
            nativeCuspStratumKernel (fun i : s => p i.val) (fun i => hp0 i.val) (fun i => hg i.val)
              (sector k s) (c₀ k) (d k s) (U k s) (κ k s) (σ k s) (ε k s) (fun i => j i.val) (Vstar W) X := by
  classical
  have hcoords (k : O ⧸ Ideal.span {9 * c}) :=
    exists_primary_cusp_coordinates (-3 * Quotient.out k) (9 * c) (mul_ne_zero (by norm_num) hc)
  choose a₀ c₀ hc₀ hcop hcdiv hprimary hratio using hcoords
  have hmode (k) : ∃ mode : Bool, if mode then lambda ^ 2 ∣ a₀ k - 1 else lambda ^ 2 ∣ c₀ k - 1 := by
    rcases hprimary k with ha | hc
    · exact ⟨true, ha⟩
    · exact ⟨false, hc⟩
  choose mode hmode using hmode
  have hNc₀ (k) : (27 : O) * c₀ k ∣ N := by
    apply dvd_trans _ hN
    obtain ⟨t, ht⟩ := hcdiv k
    refine ⟨t, ?_⟩
    linear_combination 27 * ht
  have hbranch (k : O ⧸ Ideal.span {9 * c}) (s : Finset ι) :=
    exists_native_smoothed_cusp_reflection (fun i : s => p i.val) (fun i => hp0 i.val) (fun i => hg i.val)
      (fun i l hil => hpair (by intro he; exact hil (Subtype.ext he))) (fun i => hp i.val)
      N (a₀ k) (c₀ k) (hc₀ k) (hNc₀ k) (fun i => hNp i.val) (hcop k) (mode k) (hmode k)
  choose lift M σ ε U κ hperiod hres hMa hMc hfixed hκ hreflect using hbranch
  let sector := fun k s => fixedCuspSector (M k s (fun _ => 1))
  let d₀ := fun k s => M k s (fun _ => 1) 1 1
  have hM0 (k) (s : Finset ι) (v) : M k s v 1 0 ≠ 0 := by
    rw [hMc]
    exact mul_ne_zero (hc₀ k) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i.val))
  let D := fun q : (O ⧸ Ideal.span {9 * c}) ×
      (Σ s : Finset ι, ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) =>
    fixedMatrixCusp (M q.1 q.2.1 q.2.2) (hM0 q.1 q.2.1 q.2.2)
  have hbasePoint (k) : ringComplex (a₀ k) / ringComplex (c₀ k) = thetaFourierTranslation (9 * c) k := by
    rw [hratio]
    simp only [thetaFourierTranslation, map_mul, map_neg, map_ofNat]
  have hpoint (k) (s : Finset ι) (v) : (D (k, ⟨s, v⟩)).point = thetaFourierTranslation (9 * c) k +
      ringComplex traceLambda ^ 2 * ∑ i : s, ringComplex (lift k s v i) / ringComplex (p i.val) := by
    dsimp only [D]
    rw [fixedMatrixCusp_point, hMa, hMc,
      cuspCrossNumerator_fraction (a₀ k) (c₀ k) traceLambda (fun i : s => p i.val) (lift k s v) (hc₀ k) (fun i => hp0 i.val), hbasePoint]
  refine ⟨c₀, sector, d₀, U, κ, σ, ε, (fun k => ⟨hc₀ k, hcdiv k⟩), hκ, ?_⟩
  intro W A B hA hs hW X hX
  have hVs := Vstar_support W A B hs
  have hV := Vstar_contDiff W A B hA hs hW
  rw [completedT_active_primeCusp_reflection p hp0
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)
    c hc Ψ lift hres D hpoint W A B hA hs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs'
  rw [show nativeCuspStratumKernel (fun i : s => p i.val) (fun i => hp0 i.val) (fun i => hg i.val)
      (sector k s) (c₀ k) (d₀ k s) (U k s) (κ k s) (σ k s) (ε k s) (fun i => j i.val) (Vstar W) X =
      cuspUnitSourceSum (fun i : s => p i.val) (fun i => hp0 i.val) (fun i => hg i.val)
        (c₀ k) (M k s) (fun i => j i.val) (Vstar W) X from
      (hreflect k s (fun i => j i.val) (Vstar W) A B hA hVs hV X hX).symm]
  simp only [cuspUnitSourceSum, Finset.mul_sum]
  refine Finset.sum_congr (by ext v; simp only [Finset.mem_univ]) ?_
  intro v hv
  rw [← (D (k, ⟨s, v⟩)).smoothed_reflection (Vstar W) A B hA hVs hV X hX]
  have hpoint' : (D (k, ⟨s, v⟩)).point = ringComplex (M k s v 0 0) / ringComplex (c₀ k * ∏ i : s, p i.val) := by
    dsimp only [D]
    rw [fixedMatrixCusp_point, hMc]
  rw [hpoint']
  ring

/-- Exceptional local factors expand into signed divisor terms before taking norms. -/
lemma finiteReflectionBracket_divisor_expansion {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (x : ∀ i, F i) :
    (∏ i, finiteReflectionBracket (χ i) (j i) (x i)) =
      ∑ t ∈ (Finset.univ.filter (fun i => j i = 4)).powerset,
        ((-1 : ℂ) ^ t.card * ∏ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t,
          if x i = 0 then (Fintype.card (F i) : ℂ) else 0) *
        ∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4), (χ i ^ reflectedSexticExponent (j i)) (x i) := by
  classical
  let E := Finset.univ.filter (fun i => j i = 4)
  have he : (∏ i ∈ E, finiteReflectionBracket (χ i) (j i) (x i)) =
      ∏ i ∈ E, ((if x i = 0 then (Fintype.card (F i) : ℂ) else 0) - 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [finiteReflectionBracket, if_pos (Finset.mem_filter.mp hi).2]
  have hn : (∏ i ∈ Eᶜ, finiteReflectionBracket (χ i) (j i) (x i)) =
      ∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4), (χ i ^ reflectedSexticExponent (j i)) (x i) := by
    have hc : Eᶜ = Finset.univ.filter (fun i => j i ≠ 4) := by ext i; simp [E]
    rw [hc]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [finiteReflectionBracket, if_neg (Finset.mem_filter.mp hi).2]
  rw [← Finset.prod_mul_prod_compl E, he, hn, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.sum_mul, E]

/-- The selected exceptional factors impose precisely simultaneous prime divisibility. -/
lemma finite_divisor_indicator_product {ι : Type*} (s : Finset ι)
    (p : ι → O) (q : ι → ℂ) (x : O) :
    (∏ i ∈ s, if p i ∣ x then q i else 0) =
      if ∀ i ∈ s, p i ∣ x then ∏ i ∈ s, q i else 0 := by
  classical
  by_cases h : ∀ i ∈ s, p i ∣ x
  · simp only [if_pos h]
    exact Finset.prod_congr rfl (fun i hi => if_pos (h i hi))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hn⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hn)

lemma finiteMulChar_norm_le_one {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (x : F) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp only [hx, MulChar.map_zero, norm_zero, zero_le_one]
  · exact (finiteMulChar_unit_norm χ (Units.mk0 x hx)).le

/-- One signed term in the simultaneous exceptional-prime expansion. -/
def finiteReflectionDivisorTerm {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (t : Finset ι) (x : ∀ i, F i) : ℂ :=
  ((-1 : ℂ) ^ t.card * ∏ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t,
    if x i = 0 then (Fintype.card (F i) : ℂ) else 0) *
    ∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4), (χ i ^ reflectedSexticExponent (j i)) (x i)

lemma finiteReflectionDivisorTerm_norm_le {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (t : Finset ι) (x : ∀ i, F i) :
    ‖finiteReflectionDivisorTerm χ j t x‖ ≤
      ∏ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t, (Fintype.card (F i) : ℝ) := by
  classical
  have hq (i) : ‖if x i = 0 then (Fintype.card (F i) : ℂ) else 0‖ ≤ (Fintype.card (F i) : ℝ) := by
    split_ifs <;> simp
  have hc : (∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4),
      ‖(χ i ^ reflectedSexticExponent (j i)) (x i)‖) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => finiteMulChar_norm_le_one _ _)
  simp only [finiteReflectionDivisorTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_prod]
  exact (mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hq i))
    hc (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))).trans_eq (mul_one _)

/-- Signed exceptional divisor blocks may be regrouped without estimating the reflected sum. -/
theorem tsum_finiteReflectionBracket_divisor_blocks {α ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (a : α → ℂ)
    (ha : Summable (fun h => ‖a h‖)) (x : α → ∀ i, F i) :
    (∑' h, a h * ∏ i, finiteReflectionBracket (χ i) (j i) (x h i)) =
      ∑ t ∈ (Finset.univ.filter (fun i => j i = 4)).powerset,
        ∑' h, a h * finiteReflectionDivisorTerm χ j t (x h) := by
  classical
  have hs (t : Finset ι) : Summable (fun h => a h * finiteReflectionDivisorTerm χ j t (x h)) := by
    apply Summable.of_norm_bounded
      (ha.mul_right (∏ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t, (Fintype.card (F i) : ℝ)))
    intro h
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (finiteReflectionDivisorTerm_norm_le χ j t (x h)) (norm_nonneg _)
  rw [← Summable.tsum_finsetSum (fun t _ => hs t)]
  apply tsum_congr
  intro h
  rw [finiteReflectionBracket_divisor_expansion, Finset.mul_sum]
  rfl

lemma finiteReflectionDivisorTerm_eisenstein {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (t : Finset ι) (x : O) :
    finiteReflectionDivisorTerm (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) j t
      (fun i => Ideal.Quotient.mk (Ideal.span {p i}) x) =
      ((-1 : ℂ) ^ t.card *
        (if ∀ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t, p i ∣ x then
          ∏ i ∈ (Finset.univ.filter (fun i => j i = 4)) \ t,
            (Fintype.card (O ⧸ Ideal.span {p i}) : ℂ) else 0)) *
      ∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4),
        (complexSexticChar (Ideal.span {p i}) (hg i) ^ reflectedSexticExponent (j i))
          (Ideal.Quotient.mk (Ideal.span {p i}) x) := by
  classical
  unfold finiteReflectionDivisorTerm
  simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [finite_divisor_indicator_product]
  split_ifs <;> rfl

/-- A reflected prime row has one scalar phase and explicit exceptional divisor factors. -/
theorem cuspLocalReflectedProduct_brackets {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then
        (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) ∧
      ∀ x : O, cuspLocalReflectedProduct p hp hg σ ε j x =
        β * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) x) := by
  obtain ⟨β, hn, he⟩ := finiteReflectionGauss_bracket_family
    (fun i => Ideal.span {p i}) hg hchar (fun i => residueTraceQuotientChar 1 (p i) (hp i))
    (fun i => residueTraceQuotientChar_primitive (p i) (hp i)) σ ε j hj
  exact ⟨β, hn, fun x => he (fun i => Ideal.Quotient.mk (Ideal.span {p i}) x)⟩

/-- The fixed array has the same exact squarefree–cube indexing as its cusp coefficient. -/
lemma fixedCuspRadialArray_tsum_full_index (s : FixedCuspSector) (W : O → ℂ) :
    (∑' h : O, fixedCuspRadialArray s h * W h) =
      ∑' q : ThetaFullIndex, fixedCuspRadialArray s (thetaFullFrequency q) * W (thetaFullFrequency q) := by
  exact sourceCuspRadial_tsum_full_index (fixedCuspIndex s)
    (ringComplex (fixedCuspTriangular s 0 0 * fixedCuspTriangular s 0 1)) W

/-- Canonical reflection exposes the cube labels before any absolute-value estimate. -/
theorem nativeCuspStratumKernel_full_brackets {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (s : FixedCuspSector) (c d U : O) (κ : ℂ)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then
        (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) ∧
      ∀ (V : ℝ → ℂ) (X : ℝ), nativeCuspStratumKernel p hp hg s c d U κ σ ε j V X =
        (fixedCuspReflectionScalar s (c * ∏ i, p i) * star κ * β) *
        ∑' q : ThetaFullIndex,
          (fixedCuspRadialArray s (thetaFullFrequency q) *
            paperKernel V (fixedCuspReflectionScale s (c * ∏ i, p i) X *
              (‖ringComplex lambda‖ ^ (2 * q.2.1) * completedMellinLength q.2.2))) *
          tracePhase (-(ringComplex d * ringComplex U * ringComplex
            (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0)
              (thetaFullFrequency q))) / (ringComplex traceLambda ^ 4 * ringComplex (3 * c))) *
          ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk (Ideal.span {p i})
              (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0)
                (thetaFullFrequency q))) := by
  obtain ⟨β, hn, he⟩ := cuspLocalReflectedProduct_brackets p hp hg hchar σ ε j hj
  refine ⟨β, hn, ?_⟩
  intro V X
  unfold nativeCuspStratumKernel
  simp_rw [he]
  have hr (h : O) (K P L : ℂ) :
      (fixedCuspRadialArray s h * K) * ((star κ * P) * (β * L)) =
        (star κ * β) * (fixedCuspRadialArray s h * (K * P * L)) := by ring
  simp_rw [hr]
  rw [tsum_mul_left, fixedCuspRadialArray_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]
  simp only [mul_assoc]

/-- Exact divisor regrouping of the reflected cusp series; all signed blocks remain inside the row. -/
theorem nativeCuspStratumKernel_divisor_blocks {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (s : FixedCuspSector) (c d U : O) (hc : c ≠ 0) (κ : ℂ)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then
        (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) ∧
      ∀ (V : ℝ → ℂ) (A B : ℝ), 0 < A → Function.support V ⊆ Set.Icc A B →
        ContDiff ℝ ∞ V → ∀ X : ℝ, 0 < X →
        nativeCuspStratumKernel p hp hg s c d U κ σ ε j V X =
        (fixedCuspReflectionScalar s (c * ∏ i, p i) * star κ * β) *
        ∑ t ∈ (Finset.univ.filter (fun i => j i = 4)).powerset,
        ∑' q : ThetaFullIndex,
          (fixedCuspRadialArray s (thetaFullFrequency q) *
            paperKernel V (fixedCuspReflectionScale s (c * ∏ i, p i) X *
              (‖ringComplex lambda‖ ^ (2 * q.2.1) * completedMellinLength q.2.2))) *
          tracePhase (-(ringComplex d * ringComplex U * ringComplex
            (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0)
              (thetaFullFrequency q))) / (ringComplex traceLambda ^ 4 * ringComplex (3 * c))) *
          finiteReflectionDivisorTerm (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) j t
            (fun i => Ideal.Quotient.mk (Ideal.span {p i})
              (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0)
                (thetaFullFrequency q))) := by
  classical
  obtain ⟨β, hn, he⟩ := cuspLocalReflectedProduct_brackets p hp hg hchar σ ε j hj
  refine ⟨β, hn, ?_⟩
  intro V A B hA hs hV X hX
  let n : O → O := sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0)
  let a : O → ℂ := fun h =>
    (fixedCuspRadialArray s h * paperKernel V (fixedCuspReflectionScale s (c * ∏ i, p i) X * sourceCuspRadialLength h)) *
    tracePhase (-(ringComplex d * ringComplex U * ringComplex (n h)) /
      (ringComplex traceLambda ^ 4 * ringComplex (3 * c)))
  have ha : Summable (fun h => ‖a h‖) := by
    simpa only [a, norm_mul, tracePhase_norm, mul_one] using
      fixedCuspRadialArray_kernel_norm_summable s V A B hA hs hV _
        (fixedCuspReflectionScale_pos s _ (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))) X hX)
  have hk : nativeCuspStratumKernel p hp hg s c d U κ σ ε j V X =
      (fixedCuspReflectionScalar s (c * ∏ i, p i) * star κ * β) *
        ∑' h : O, a h * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (n h)) := by
    calc
      _ = fixedCuspReflectionScalar s (c * ∏ i, p i) * ((star κ * β) *
          ∑' h : O, a h * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk (Ideal.span {p i}) (n h))) := by
        unfold nativeCuspStratumKernel
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro h
        rw [he]
        dsimp only [a, n]
        ring
      _ = _ := by ring
  rw [hk, tsum_finiteReflectionBracket_divisor_blocks _ j a ha]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [a, n]
  simp only [mul_assoc]
  rw [fixedCuspRadialArray_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

/-- Cubing the argument retains exactly the quadratic parity of a sextic character power. -/
lemma sextic_character_cube_parity {F : Type*} [Field F]
    (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) (k : ℕ) (a b : F) :
    (χ ^ k) (a * b ^ 3) = (χ ^ k) a * (χ ^ (3 * (k % 2))) b := by
  have he : k * 3 = 6 * (k / 2) + 3 * (k % 2) := by omega
  rw [map_mul, map_pow, ← MulChar.pow_apply' (χ ^ k) (by decide : (3 : ℕ) ≠ 0),
    ← pow_mul, he, pow_add, pow_mul, hχ, one_pow, one_mul]

lemma reflectedSexticExponent_parity (j : ℕ) (hj : j < 6) :
    reflectedSexticExponent j % 2 = j % 2 := by
  interval_cases j <;> norm_num [reflectedSexticExponent]

/-- The cube factor in every nonexceptional reflected row carries only a quadratic character. -/
lemma reflected_sextic_cube_parity (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (j : ℕ) (hj : j < 6) (a b : O ⧸ P) :
    (complexSexticChar P hg ^ reflectedSexticExponent j) (a * b ^ 3) =
      (complexSexticChar P hg ^ reflectedSexticExponent j) a *
        (complexSexticChar P hg ^ (3 * (j % 2))) b := by
  rw [sextic_character_cube_parity _ (complexSexticChar_powers P hg).2.2,
    reflectedSexticExponent_parity j hj]

/-- The simultaneous reflected cube character separates before the squarefree and cube sums. -/
theorem reflected_character_product_cube_parity {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (a b : O) :
    (∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4),
      (complexSexticChar (P i) (hg i) ^ reflectedSexticExponent (j i))
        (Ideal.Quotient.mk (P i) (a * b ^ 3))) =
      (∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4),
        (complexSexticChar (P i) (hg i) ^ reflectedSexticExponent (j i)) (Ideal.Quotient.mk (P i) a)) *
      ∏ i ∈ Finset.univ.filter (fun i => j i ≠ 4),
        (complexSexticChar (P i) (hg i) ^ (3 * (j i % 2))) (Ideal.Quotient.mk (P i) b) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_mul, map_pow, reflected_sextic_cube_parity _ _ _ (hj i)]

/-- The exceptional divisor condition splits into disjoint squarefree and cube cases. -/
lemma prime_divisor_cube_indicator (p a b : O) (hp : Prime p) :
    (if p ∣ a * b ^ 3 then (1 : ℂ) else 0) =
      (if p ∣ a then 1 else 0) + (if ¬ p ∣ a ∧ p ∣ b then 1 else 0) := by
  have hd : p ∣ a * b ^ 3 ↔ p ∣ a ∨ p ∣ b := by
    rw [hp.dvd_mul]
    constructor
    · exact fun h => h.elim Or.inl (fun hb => Or.inr (hp.dvd_of_dvd_pow hb))
    · exact fun h => h.elim Or.inl (fun hb => Or.inr (dvd_pow hb (by decide)))
  by_cases ha : p ∣ a <;> by_cases hb : p ∣ b <;> simp only [hd, ha, hb, or_true,
    true_or, false_or, not_true_eq_false, not_false_eq_true, and_true, and_false,
    false_and, true_and, reduceIte] <;> norm_num

/-- An omitted prime contributes its coprimality density exactly when its row exponent vanishes. -/
lemma finiteAdditiveFourier_sextic_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj : j < 6) :
    finiteAdditiveFourierCoeff ψ (complexSexticChar P hg ^ j : MulChar (O ⧸ P) ℂ) 0 =
      if j = 0 then ((Fintype.card (O ⧸ P) : ℂ) - 1) / Fintype.card (O ⧸ P) else 0 := by
  rw [finiteAdditiveFourierCoeff_mulChar_zero]
  by_cases hj0 : j = 0
  · simp only [hj0, pow_zero, reduceIte]
    rw [Nat.card_eq_fintype_card, Fintype.card_units,
      Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  · rw [if_neg (complexSexticChar_pow_ne_one P hg hchar j hj hj0), if_neg hj0]

/-- Away from the fixed modulus, the integral cusp frequency differs from the original by a unit. -/
theorem sourceCuspIntegralPhaseNumerator_quotient_unit (p N : O)
    [hp : (Ideal.span {p}).IsMaximal] (hN : (9 : O) ∣ N) (hNp : IsCoprime N p)
    (s : FixedCuspSector) :
    ∃ u : (O ⧸ Ideal.span {p})ˣ, ∀ h : O,
      Ideal.Quotient.mk (Ideal.span {p})
        (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h) =
        (u : O ⧸ Ideal.span {p}) * Ideal.Quotient.mk (Ideal.span {p}) h := by
  let q := Ideal.Quotient.mk (Ideal.span {p})
  have h3N : (3 : O) ∣ N := (show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans hN
  have hlN : traceLambda ∣ N := (show traceLambda ∣ (9 : O) from
    ⟨traceLambda ^ 3, by rw [← traceLambda_pow_four]; ring⟩).trans hN
  have h3 : IsUnit (q 3) := (isUnit_quotient_span_iff p 3).mpr
    (hNp.of_isCoprime_of_dvd_left h3N).symm
  have hl : IsUnit (q traceLambda) := (isUnit_quotient_span_iff p traceLambda).mpr
    (hNp.of_isCoprime_of_dvd_left hlN).symm
  have hu : IsUnit (q (fixedCuspTriangular s 0 0)) :=
    (fixedCuspTriangular_properties s).2.1.map q
  have hfactor : IsUnit (q ((if fixedCuspIndex s = 0 then 3 else 1) * traceLambda *
      fixedCuspTriangular s 0 0 ^ 2)) := by
    rw [map_mul, map_mul, map_pow]
    apply IsUnit.mul _ (hu.pow 2)
    apply IsUnit.mul _ hl
    split_ifs
    · exact h3
    · exact isUnit_one
  obtain ⟨u, he⟩ := hfactor
  refine ⟨u, ?_⟩
  intro h
  change q (_ * h) = (u : O ⧸ Ideal.span {p}) * q h
  rw [map_mul, ← he]

/-- Unit changes of local coordinates contribute a single norm-one row factor. -/
theorem finiteReflectionBracket_unit_family {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (u : ∀ i, (F i)ˣ) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ x : ∀ i, F i,
      (∏ i, finiteReflectionBracket (χ i) (j i) ((u i : F i) * x i)) =
        γ * ∏ i, finiteReflectionBracket (χ i) (j i) (x i) := by
  refine ⟨∏ i, finiteReflectionUnitFactor (χ i) (j i) (u i), ?_, ?_⟩
  · simp only [norm_prod, finiteReflectionUnitFactor_norm, Finset.prod_const_one]
  · intro x
    simp only [finiteReflectionBracket_unit_mul, Finset.prod_mul_distrib]

/-- A nonzero integral frequency scaling changes only the constant phase of a reflected row. -/
theorem cuspLocalReflectedProduct_original_frequency {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (N : O) (hN : (9 : O) ∣ N) (hNp : ∀ i, IsCoprime N (p i)) (s : FixedCuspSector)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then
        (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) ∧
      ∀ h : O, cuspLocalReflectedProduct p hp hg σ ε j
          (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h) =
        β * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) h) := by
  classical
  choose u hu using fun i => sourceCuspIntegralPhaseNumerator_quotient_unit (p i) N hN (hNp i) s
  obtain ⟨β, hn, he⟩ := cuspLocalReflectedProduct_brackets p hp hg hchar σ ε j hj
  obtain ⟨γ, hγ, hγe⟩ := finiteReflectionBracket_unit_family
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) j u
  refine ⟨β * γ, ?_, ?_⟩
  · rw [norm_mul, mul_pow, hγ, one_pow, mul_one, hn]
  · intro h
    rw [he]
    simp_rw [hu]
    rw [hγe, mul_assoc]

/-- Reflected arithmetic coefficients range over a fixed residue modulus, independently of the prime row. -/
def fixedCuspPeriodicArray (N c : O) (s : FixedCuspSector)
    (b : O ⧸ Ideal.span {N}) (h : O) : ℂ :=
  fixedCuspRadialArray s h * fixedCuspInversePhase s c (Quotient.out b) h

lemma fixedCuspPeriodicArray_norm (N c : O) (s : FixedCuspSector)
    (b : O ⧸ Ideal.span {N}) (h : O) :
    ‖fixedCuspPeriodicArray N c s b h‖ = ‖fixedCuspRadialArray s h‖ := by
  rw [fixedCuspPeriodicArray, norm_mul, fixedCuspInversePhase_norm, mul_one]

lemma fixedCuspInversePhase_residue (N c d : O) (hc : c ≠ 0) (hN : 27 * c ∣ N)
    (s : FixedCuspSector) (h : O) :
    fixedCuspInversePhase s c d h =
      fixedCuspInversePhase s c (Quotient.out (Ideal.Quotient.mk (Ideal.span {N}) d)) h := by
  have hmod : N ∣ d - Quotient.out (Ideal.Quotient.mk (Ideal.span {N}) d) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _).symm)
  have he := cuspInverse_fixed_phase_congr (3 * c) d
    (Quotient.out (Ideal.Quotient.mk (Ideal.span {N}) d)) 1
    (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h)
    (mul_ne_zero (by norm_num) hc) (((cuspInverse_fixed_modulus_dvd c).trans hN).trans hmod)
  simpa only [fixedCuspInversePhase, map_one, mul_one] using he

lemma fixedCuspPeriodicArray_tsum_full_index (N c : O) (s : FixedCuspSector)
    (b : O ⧸ Ideal.span {N}) (W : O → ℂ) :
    (∑' h : O, fixedCuspPeriodicArray N c s b h * W h) =
      ∑' q : ThetaFullIndex, fixedCuspPeriodicArray N c s b (thetaFullFrequency q) * W (thetaFullFrequency q) := by
  simp only [fixedCuspPeriodicArray, mul_assoc]
  exact fixedCuspRadialArray_tsum_full_index s _

lemma fixedCuspPeriodicArray_kernel_norm_summable (N c : O) (s : FixedCuspSector)
    (b : O ⧸ Ideal.span {N}) (V : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hs : Function.support V ⊆ Set.Icc A B) (hV : ContDiff ℝ ∞ V) (R : ℝ) (hR : 0 < R) :
    Summable (fun h : O => ‖fixedCuspPeriodicArray N c s b h * paperKernel V (R * sourceCuspRadialLength h)‖) := by
  simpa only [norm_mul, fixedCuspPeriodicArray_norm] using
    fixedCuspRadialArray_kernel_norm_summable s V A B hA hs hV R hR

lemma fixedCuspReflectionScale_prime_product {ι : Type*} [Fintype ι]
    (p : ι → O) (s : FixedCuspSector) (c : O) (X : ℝ) :
    fixedCuspReflectionScale s (c * ∏ i, p i) X =
      fixedCuspReflectionScale s c (X / ‖ringComplex (∏ i, p i)‖ ^ 4) := by
  unfold fixedCuspReflectionScale
  rw [map_mul, norm_mul, mul_pow]
  ring

lemma fixedCuspReflectionScalar_norm (s : FixedCuspSector) (c : O) (hc : c ≠ 0) :
    ‖fixedCuspReflectionScalar s c‖ = (sourceCuspScale (fixedCuspIndex s)) ^ 2 := by
  obtain ⟨u, hu⟩ := (fixedCuspTriangular_properties s).2.1
  have hn : ‖ringComplex (fixedCuspTriangular s 0 0)‖ = 1 := by
    rw [← hu]
    exact norm_ringComplex_unit u
  have hc' : ‖ringComplex c‖ ≠ 0 := (norm_pos_iff.mpr (ringComplex_ne_zero hc)).ne'
  simp only [fixedCuspReflectionScalar, norm_mul, norm_neg, norm_pow, norm_div, norm_star,
    hn, one_pow, div_self hc', one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceCuspScale_pos _)]

lemma fixedCuspReflectionScalar_norm_sq_le (s : FixedCuspSector) (c : O) (hc : c ≠ 0) :
    ‖fixedCuspReflectionScalar s c‖ ^ 2 ≤ 81 := by
  rw [fixedCuspReflectionScalar_norm s c hc]
  have hs : (sourceCuspScale (fixedCuspIndex s)) ^ 2 ≤ 9 := by
    generalize fixedCuspIndex s = j
    fin_cases j <;> norm_num [sourceCuspScale]
  exact (pow_le_pow_left₀ (sq_nonneg _) hs 2).trans_eq (by norm_num)

/-- Signed divisor blocks built from a fixed cusp coefficient array and quadratic cube characters. -/
def fixedCuspDivisorSeries {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N c : O) (s : FixedCuspSector) (b : O ⧸ Ideal.span {N}) (j : ι → ℕ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ t ∈ (Finset.univ.filter (fun i => j i = 4)).powerset,
    ∑' q : ThetaFullIndex,
      (fixedCuspPeriodicArray N c s b (thetaFullFrequency q) *
        paperKernel V (fixedCuspReflectionScale s c (X / ‖ringComplex (∏ i, p i)‖ ^ 4) *
          (‖ringComplex lambda‖ ^ (2 * q.2.1) * completedMellinLength q.2.2))) *
      finiteReflectionDivisorTerm (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) j t
        (fun i => Ideal.Quotient.mk (Ideal.span {p i}) (thetaFullFrequency q))

/-- The arithmetic reflection is an exact finite-modulus divisor series with the sharp Gauss normalization. -/
theorem nativeCuspStratumKernel_canonical {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (N c d U : O) (hc : c ≠ 0) (hN : 27 * c ∣ N) (hNp : ∀ i, IsCoprime N (p i))
    (s : FixedCuspSector) (κ : ℂ) (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ β : ℂ, ‖β‖ ^ 2 = (∏ i, if j i = 0 ∨ j i = 4 then
        (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) ∧
      ∀ (V : ℝ → ℂ) (A B : ℝ), 0 < A → Function.support V ⊆ Set.Icc A B →
        ContDiff ℝ ∞ V → ∀ X : ℝ, 0 < X →
        nativeCuspStratumKernel p hp hg s c d U κ σ ε j V X =
          (fixedCuspReflectionScalar s (c * ∏ i, p i) * star κ * β) *
          fixedCuspDivisorSeries p hg N c s (Ideal.Quotient.mk (Ideal.span {N}) (d * U)) j V X := by
  classical
  have h9N : (9 : O) ∣ N := (show (9 : O) ∣ 27 * c from ⟨3 * c, by ring⟩).trans hN
  obtain ⟨β, hn, he⟩ := cuspLocalReflectedProduct_original_frequency p hp hg hchar N h9N hNp s σ ε j hj
  refine ⟨β, hn, ?_⟩
  intro V A B hA hs hV X hX
  let b := Ideal.Quotient.mk (Ideal.span {N}) (d * U)
  let R := fixedCuspReflectionScale s c (X / ‖ringComplex (∏ i, p i)‖ ^ 4)
  have hpR : 0 < R := by
    dsimp only [R]
    rw [← fixedCuspReflectionScale_prime_product p s c X]
    exact fixedCuspReflectionScale_pos s _ (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))) X hX
  let a : O → ℂ := fun h => fixedCuspPeriodicArray N c s b h * paperKernel V (R * sourceCuspRadialLength h)
  have ha : Summable (fun h => ‖a h‖) := fixedCuspPeriodicArray_kernel_norm_summable N c s b V A B hA hs hV R hpR
  have hphase (h : O) : tracePhase (-(ringComplex d * ringComplex U * ringComplex
      (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h)) /
      (ringComplex traceLambda ^ 4 * ringComplex (3 * c))) = fixedCuspInversePhase s c (Quotient.out b) h := by
    simpa only [fixedCuspInversePhase, map_mul, b] using fixedCuspInversePhase_residue N c (d * U) hc hN s h
  have hk : nativeCuspStratumKernel p hp hg s c d U κ σ ε j V X =
      (fixedCuspReflectionScalar s (c * ∏ i, p i) * star κ * β) *
        ∑' h : O, a h * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) h) := by
    calc
      _ = fixedCuspReflectionScalar s (c * ∏ i, p i) * ((star κ * β) *
          ∑' h : O, a h * ∏ i, finiteReflectionBracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk (Ideal.span {p i}) h)) := by
        unfold nativeCuspStratumKernel
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro h
        rw [he, hphase, fixedCuspReflectionScale_prime_product]
        dsimp only [a, R, fixedCuspPeriodicArray]
        ring
      _ = _ := by ring
  rw [hk, tsum_finiteReflectionBracket_divisor_blocks _ j a ha]
  unfold fixedCuspDivisorSeries
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [a, b, R]
  simp only [mul_assoc]
  rw [fixedCuspPeriodicArray_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

/-- Squared Gauss normalization at an active prime. -/
def reflectedActiveMass (q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = 4 then q⁻¹ else 1

/-- Density of the zero Fourier frequency at an inactive prime. -/
def reflectedInactiveMass (q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 - q⁻¹ else 0

lemma reflectedActiveMass_nonneg (q : ℝ) (hq : 0 ≤ q) (j : ℕ) :
    0 ≤ reflectedActiveMass q j := by
  unfold reflectedActiveMass
  split_ifs <;> positivity

lemma reflectedInactiveMass_nonneg (q : ℝ) (hq : 1 ≤ q) (j : ℕ) :
    0 ≤ reflectedInactiveMass q j := by
  unfold reflectedInactiveMass
  split_ifs
  · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)
  · exact le_rfl

/-- Summing every active-prime stratum preserves total mass; only the fourth-power primes cost density. -/
theorem reflected_branch_mass {ι : Type*} [Fintype ι] (q : ι → ℝ) (j : ι → ℕ) :
    (∑ s : Finset ι, (∏ i ∈ s, reflectedActiveMass (q i) (j i)) *
      ∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i)) =
      ∏ i, if j i = 4 then (q i)⁻¹ else 1 := by
  classical
  rw [← Fintype.prod_add]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h0 : j i = 0
  · simp [reflectedActiveMass, reflectedInactiveMass, h0] <;> ring
  · by_cases h4 : j i = 4
    · simp [reflectedActiveMass, reflectedInactiveMass, h0, h4] <;> ring
    · simp [reflectedActiveMass, reflectedInactiveMass, h0, h4] <;> ring

lemma finiteAdditiveFourier_sextic_zero_real (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj : j < 6) :
    finiteAdditiveFourierCoeff ψ (complexSexticChar P hg ^ j : MulChar (O ⧸ P) ℂ) 0 =
      (reflectedInactiveMass (Fintype.card (O ⧸ P)) j : ℂ) := by
  rw [finiteAdditiveFourier_sextic_zero P hg hchar ψ j hj]
  unfold reflectedInactiveMass
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos h0]
    push_cast
    have hq : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [if_neg h0, Complex.ofReal_zero]

lemma finiteAdditiveFourier_inactive_sextic_density {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (ψ : ∀ i, AddChar (O ⧸ P i) ℂ)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (s : Finset ι) :
    (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (ψ i.val)
      (complexSexticChar (P i.val) (hg i.val) ^ j i.val : MulChar (O ⧸ P i.val) ℂ) 0) =
      ((∏ i ∈ sᶜ, reflectedInactiveMass (Fintype.card (O ⧸ P i)) (j i) : ℝ) : ℂ) := by
  classical
  rw [Finset.prod_subtype (F := inferInstanceAs (Fintype {i // i ∉ s})) sᶜ (fun _ => Finset.mem_compl)]
  push_cast
  exact Finset.prod_congr rfl (fun i _ => finiteAdditiveFourier_sextic_zero_real
    (P i.val) (hg i.val) (hchar i.val) (ψ i.val) (j i.val) (hj i.val))

/-- Weighted Cauchy–Schwarz keeps inactive-prime densities in both energies. -/
theorem finite_density_energy_bound {ι : Type*} [Fintype ι]
    (D A : ι → ℝ) (phase F : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ i, 0 ≤ D i) (hA : ∀ i, 0 ≤ A i) (hphase : ∀ i, ‖phase i‖ ^ 2 ≤ C * A i) :
    ‖∑ i, (D i : ℂ) * phase i * F i‖ ^ 2 ≤
      C * (∑ i, D i * A i) * ∑ i, D i * ‖F i‖ ^ 2 := by
  classical
  have hn : ‖∑ i, (D i : ℂ) * phase i * F i‖ ≤ ∑ i, D i * ‖phase i‖ * ‖F i‖ := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hD i)]
  have hpoint (i) : (D i * ‖phase i‖ * ‖F i‖) ^ 2 ≤
      (D i * A i) * (C * D i * ‖F i‖ ^ 2) := by
    calc
      _ = (D i ^ 2 * ‖F i‖ ^ 2) * ‖phase i‖ ^ 2 := by ring
      _ ≤ (D i ^ 2 * ‖F i‖ ^ 2) * (C * A i) :=
        mul_le_mul_of_nonneg_left (hphase i) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => mul_nonneg (hD i) (hA i))
    (fun i _ => mul_nonneg (mul_nonneg hC (hD i)) (sq_nonneg _)) (fun i _ => hpoint i)
  apply ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs).trans_eq
  rw [show (∑ i, C * D i * ‖F i‖ ^ 2) = C * ∑ i, D i * ‖F i‖ ^ 2 by
    simp only [Finset.mul_sum, mul_assoc]]
  ring

/-- Active-stratum reflection costs only the exceptional fourth-power density in the first energy. -/
theorem reflected_stratum_energy_bound {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : ∀ i, 1 ≤ q i) (j : ι → ℕ)
    (phase F : Finset ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hphase : ∀ s : Finset ι, ‖phase s‖ ^ 2 ≤ C * ∏ i ∈ s, reflectedActiveMass (q i) (j i)) :
    ‖∑ s : Finset ι, ((∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i) : ℝ) : ℂ) * phase s * F s‖ ^ 2 ≤
      C * (∏ i, if j i = 4 then (q i)⁻¹ else 1) *
        ∑ s : Finset ι, (∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i)) * ‖F s‖ ^ 2 := by
  classical
  have he := finite_density_energy_bound
    (fun s : Finset ι => ∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i))
    (fun s : Finset ι => ∏ i ∈ s, reflectedActiveMass (q i) (j i)) phase F C hC
    (fun s => Finset.prod_nonneg (fun i _ => reflectedInactiveMass_nonneg _ (hq i) _))
    (fun s => Finset.prod_nonneg (fun i _ => reflectedActiveMass_nonneg _ (zero_le_one.trans (hq i)) _)) hphase
  have hm : (∑ s : Finset ι, (∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i)) *
      ∏ i ∈ s, reflectedActiveMass (q i) (j i)) = ∏ i, if j i = 4 then (q i)⁻¹ else 1 := by
    simpa only [mul_comm] using reflected_branch_mass q j
  rwa [hm] at he

/-- Completed Gauss rows are finite sums of canonical divisor series with uniformly bounded cusp multipliers. -/
theorem completedT_canonical_divisor_reflection {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp0 : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hp : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (N c : O) (hc : c ≠ 0) (hN : (243 : O) * c ∣ N) (hNp : ∀ i, IsCoprime N (p i))
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ (c₀ : (O ⧸ Ideal.span {9 * c}) → O)
      (sector : (O ⧸ Ideal.span {9 * c}) → Finset ι → FixedCuspSector)
      (b : (O ⧸ Ideal.span {9 * c}) → Finset ι → (O ⧸ Ideal.span {N}))
      (phase : (O ⧸ Ideal.span {9 * c}) → Finset ι → ℂ),
      (∀ k, c₀ k ≠ 0 ∧ c₀ k ∣ 9 * c) ∧
      (∀ k s, ‖phase k s‖ ^ 2 ≤ 81 * ∏ i : s,
        if j i.val = 0 ∨ j i.val = 4 then (Fintype.card (O ⧸ Ideal.span {p i.val}) : ℝ)⁻¹ else 1) ∧
      ∀ (W : ℝ → ℂ) (A B : ℝ), 0 < A → Function.support W ⊆ Set.Icc A B →
        ContDiff ℝ ∞ W → ∀ X : ℝ, 0 < X →
        completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom *
          primeCuspRowCharacter p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)) W X =
        thetaDerivativeScalar⁻¹ * ∑ k : O ⧸ Ideal.span {9 * c},
          finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
            (finiteThetaTwist c Ψ) k *
          ∑ s : Finset ι,
            (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp0 i.val))
              (complexSexticChar (Ideal.span {p i.val}) (hg i.val) ^ j i.val : MulChar (O ⧸ Ideal.span {p i.val}) ℂ) 0) *
            phase k s * fixedCuspDivisorSeries (fun i : s => p i.val) (fun i => hg i.val)
              N (c₀ k) (sector k s) (b k s) (fun i => j i.val) (Vstar W) X := by
  classical
  obtain ⟨c₀, sector, d, U, κ, σ, ε, hc₀, hκ, hrow⟩ :=
    completedT_constructed_active_reflection p hp0 hg hp hpair N c hc hN hNp Ψ j
  have hNc₀ (k) : (27 : O) * c₀ k ∣ N := by
    apply dvd_trans _ hN
    obtain ⟨t, ht⟩ := (hc₀ k).2
    refine ⟨t, ?_⟩
    linear_combination 27 * ht
  have hbranch (k : O ⧸ Ideal.span {9 * c}) (s : Finset ι) :=
    nativeCuspStratumKernel_canonical (fun i : s => p i.val) (fun i => hp0 i.val)
      (fun i => hg i.val) (fun i => hchar i.val) N (c₀ k) (d k s) (U k s)
      (hc₀ k).1 (hNc₀ k) (fun i => hNp i.val) (sector k s) (κ k s) (σ k s) (ε k s)
      (fun i => j i.val) (fun i => hj i.val)
  choose β hβnorm hβ using hbranch
  let b := fun k s => Ideal.Quotient.mk (Ideal.span {N}) (d k s * U k s)
  let phase := fun k (s : Finset ι) =>
    fixedCuspReflectionScalar (sector k s) (c₀ k * ∏ i : s, p i.val) * star (κ k s) * β k s
  refine ⟨c₀, sector, b, phase, hc₀, ?_, ?_⟩
  · intro k s
    dsimp only [phase]
    rw [norm_mul, norm_mul, norm_star, hκ, mul_one, mul_pow, hβnorm]
    apply mul_le_mul_of_nonneg_right
      (fixedCuspReflectionScalar_norm_sq_le _ _
        (mul_ne_zero (hc₀ k).1 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i.val))))
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> positivity
  · intro W A B hA hs hW X hX
    rw [hrow W A B hA hs hW X hX]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.sum_congr rfl
    intro s hs'
    rw [hβ k s (Vstar W) A B hA (Vstar_support W A B hs) (Vstar_contDiff W A B hA hs hW) X hX]
    dsimp only [b, phase]
    ring

/-- The reflection constant depends only on the fixed finite character. -/
def completedReflectionConstant (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) : ℝ :=
  81 * ‖thetaDerivativeScalar⁻¹‖ ^ 2 * ∑ k : O ⧸ Ideal.span {9 * c},
    ‖finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c Ψ) k‖ ^ 2

/-- Uniform first-reflection energy: signed divisor sums remain intact, while active-prime masses sum exactly. -/
theorem completedT_canonical_energy {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp0 : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hp : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (N c : O) (hc : c ≠ 0) (hN : (243 : O) * c ∣ N) (hNp : ∀ i, IsCoprime N (p i))
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ (c₀ : (O ⧸ Ideal.span {9 * c}) → O)
      (sector : (O ⧸ Ideal.span {9 * c}) → Finset ι → FixedCuspSector)
      (b : (O ⧸ Ideal.span {9 * c}) → Finset ι → (O ⧸ Ideal.span {N})),
      (∀ k, c₀ k ≠ 0 ∧ c₀ k ∣ 9 * c) ∧
      ∀ (W : ℝ → ℂ) (A B : ℝ), 0 < A → Function.support W ⊆ Set.Icc A B →
        ContDiff ℝ ∞ W → ∀ X : ℝ, 0 < X →
        ‖completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom *
          primeCuspRowCharacter p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)) W X‖ ^ 2 ≤
        completedReflectionConstant c hc Ψ *
          (∏ i, if j i = 4 then (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)⁻¹ else 1) *
          ∑ k : O ⧸ Ideal.span {9 * c}, ∑ s : Finset ι,
            (∏ i ∈ sᶜ, reflectedInactiveMass (Fintype.card (O ⧸ Ideal.span {p i})) (j i)) *
            ‖fixedCuspDivisorSeries (fun i : s => p i.val) (fun i => hg i.val)
              N (c₀ k) (sector k s) (b k s) (fun i => j i.val) (Vstar W) X‖ ^ 2 := by
  classical
  obtain ⟨c₀, sector, b, phase, hc₀, hphase, hrow⟩ :=
    completedT_canonical_divisor_reflection p hp0 hg hp hchar hpair N c hc hN hNp Ψ j hj
  refine ⟨c₀, sector, b, hc₀, ?_⟩
  intro W A B hA hs hW X hX
  let q : ι → ℝ := fun i => Fintype.card (O ⧸ Ideal.span {p i})
  let D : Finset ι → ℝ := fun s => ∏ i ∈ sᶜ, reflectedInactiveMass (q i) (j i)
  let F := fun (k : O ⧸ Ideal.span {9 * c}) (s : Finset ι) =>
    fixedCuspDivisorSeries (fun i : s => p i.val) (fun i => hg i.val)
      N (c₀ k) (sector k s) (b k s) (fun i => j i.val) (Vstar W) X
  let T := fun k => ∑ s : Finset ι, (D s : ℂ) * phase k s * F k s
  let base := finiteAdditiveFourierCoeff
    (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ)
  let Q : ℝ := ∏ i, if j i = 4 then (q i)⁻¹ else 1
  have hq (i) : 1 ≤ q i := by
    change (1 : ℝ) ≤ (Fintype.card (O ⧸ Ideal.span {p i}) : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (@Fintype.card_pos (O ⧸ Ideal.span {p i}) _ _)
  have hrow' : completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom *
      primeCuspRowCharacter p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)) W X =
      thetaDerivativeScalar⁻¹ * ∑ k, base k * T k := by
    rw [hrow W A B hA hs hW X hX]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.sum_congr rfl
    intro s hs'
    rw [finiteAdditiveFourier_inactive_sextic_density (fun i => Ideal.span {p i}) hg hchar
      (fun i => residueTraceQuotientChar 1 (p i) (hp0 i)) j hj s]
  have hinner (k) : ‖T k‖ ^ 2 ≤ 81 * Q * ∑ s : Finset ι, D s * ‖F k s‖ ^ 2 := by
    apply reflected_stratum_energy_bound q hq j (phase k) (F k) 81 (by norm_num)
    intro s
    rw [Finset.prod_subtype (F := inferInstanceAs (Fintype s)) s (fun _ => Iff.rfl)]
    exact hphase k s
  have hsum : (∑ k, ‖T k‖ ^ 2) ≤ 81 * Q * ∑ k, ∑ s : Finset ι, D s * ‖F k s‖ ^ 2 := by
    calc
      _ ≤ ∑ k, 81 * Q * ∑ s : Finset ι, D s * ‖F k s‖ ^ 2 := Finset.sum_le_sum (fun k _ => hinner k)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have houter : ‖∑ k, base k * T k‖ ^ 2 ≤ (∑ k, ‖base k‖ ^ 2) * ∑ k, ‖T k‖ ^ 2 := by
    simpa only [Complex.ofReal_one, one_mul] using
      finite_density_energy_bound (fun _ => 1) (fun k => ‖base k‖ ^ 2) base T 1 (by norm_num)
        (fun _ => by norm_num) (fun _ => sq_nonneg _) (fun _ => by simp only [one_mul, le_refl])
  rw [hrow', norm_mul, mul_pow]
  apply (mul_le_mul_of_nonneg_left houter (sq_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (sq_nonneg _)).trans_eq
  dsimp only [completedReflectionConstant, base, Q, q, D, F]
  ring

/-- Uniform constants for the three exact cusp coefficient families. -/
def sourceCuspCoefficientBaseBound (j : Fin 3) : ℝ :=
  if j = 0 then sourceCoefficientBaseBound
  else ramifiedCoefficientBaseBound (ramifiedCuspRoot (decide (j = 2))) (ramifiedCuspScaleUnit (decide (j = 2)))

lemma sourceCuspCoefficientBaseBound_nonneg (j : Fin 3) : 0 ≤ sourceCuspCoefficientBaseBound j := by
  fin_cases j
  · exact sourceCoefficientBaseBound_nonneg
  · exact ramifiedCoefficientBaseBound_nonneg _ _
  · exact ramifiedCoefficientBaseBound_nonneg _ _

lemma sourceCuspCoefficient_full_bound (j : Fin 3) (q : ThetaFullIndex) :
    ‖sourceCuspCoefficient j (thetaFullFrequency q)‖ ≤ sourceCuspCoefficientBaseBound j *
      ‖ringComplex ((q.1 : O) * lambda ^ q.2.1)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator q.2.2.2.val)‖ := by
  fin_cases j
  · exact rationalSourceResidualFourierCoefficient_squarefree_cube_bound _ _
      q.2.2.1.property.2 q.2.2.2.property q.2.2.1.property.1 q.1 q.2.1
  · exact ramifiedResidualFourierCoefficient_squarefree_cube_bound _ _ _ _
      q.2.2.1.property.2 q.2.2.2.property q.2.2.1.property.1 q.1 q.2.1
  · exact ramifiedResidualFourierCoefficient_squarefree_cube_bound _ _ _ _
      q.2.2.1.property.2 q.2.2.2.property q.2.2.1.property.1 q.1 q.2.1

/-- Differentiation contributes one inverse radial norm after Bessel normalization. -/
lemma sourceCuspRadialBaseCoefficient_norm_exact (j : Fin 3) (h : O) (hh : h ≠ 0) :
    ‖sourceCuspRadialBaseCoefficient j h‖ =
      (‖-2 * Real.pi * Complex.I * thetaFrequencyScale‖ / (sourceCuspScale j) ^ 2) *
        (‖sourceCuspCoefficient j h‖ / ‖ringComplex h‖) := by
  have hh' : ‖ringComplex h‖ ≠ 0 := (norm_pos_iff.mpr (ringComplex_ne_zero hh)).ne'
  have hs : sourceCuspScale j ≠ 0 := (sourceCuspScale_pos j).ne'
  have he : -2 * Real.pi * Complex.I * cuspFrequency h =
      (-2 * Real.pi * Complex.I * thetaFrequencyScale) * ringComplex h := by
    rw [cuspFrequency_eq_thetaFrequencyScale]
    ring
  have hS : ‖(sourceCuspScale j : ℂ)‖ = sourceCuspScale j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sourceCuspScale_pos j)]
  have hL : ‖(sourceCuspRadialLength h : ℂ)‖ = ‖ringComplex h‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sourceCuspRadialLength_pos h),
      sourceCuspRadialLength, if_neg hh]
  rw [sourceCuspRadialBaseCoefficient, he]
  simp only [norm_div, norm_mul, norm_star, norm_pow, hS, hL]
  field_simp [hh', hs] <;> ring

/-- Sharp squarefree–cube decay of the radial coefficient, before localization. -/
lemma fixedCuspPeriodicArray_full_bound (N c : O) (s : FixedCuspSector)
    (b : O ⧸ Ideal.span {N}) (q : ThetaFullIndex) :
    ‖fixedCuspPeriodicArray N c s b (thetaFullFrequency q)‖ ≤
      (‖-2 * Real.pi * Complex.I * thetaFrequencyScale‖ /
        (sourceCuspScale (fixedCuspIndex s)) ^ 2 * sourceCuspCoefficientBaseBound (fixedCuspIndex s)) *
      (‖ringComplex ((q.1 : O) * lambda ^ q.2.1)‖ ^ (1 / 3 : ℝ) /
        ‖ringComplex ((q.1 : O) * lambda ^ q.2.1)‖) /
      (‖ringComplex (primaryIdealGenerator q.2.2.1.val)‖ *
        ‖ringComplex (primaryIdealGenerator q.2.2.2.val)‖ ^ 2) := by
  have hr : ‖ringComplex ((q.1 : O) * lambda ^ q.2.1)‖ ≠ 0 :=
    (norm_pos_iff.mpr (ringComplex_ne_zero (mul_ne_zero q.1.ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero)))).ne'
  have hI : ‖ringComplex (primaryIdealGenerator q.2.2.1.val)‖ ≠ 0 :=
    (norm_pos_iff.mpr (ringComplex_ne_zero q.2.2.1.property.2)).ne'
  have hJ : ‖ringComplex (primaryIdealGenerator q.2.2.2.val)‖ ≠ 0 :=
    (norm_pos_iff.mpr (ringComplex_ne_zero q.2.2.2.property)).ne'
  rw [fixedCuspPeriodicArray_norm, fixedCuspRadialArray_norm,
    sourceCuspRadialBaseCoefficient_norm_exact _ _ (thetaFullFrequency_ne_zero q)]
  apply (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sourceCuspCoefficient_full_bound (fixedCuspIndex s) q) (norm_nonneg _))
    (div_nonneg (norm_nonneg _) (sq_nonneg _))).trans_eq
  have he : ‖ringComplex (thetaFullFrequency q)‖ =
      ‖ringComplex ((q.1 : O) * lambda ^ q.2.1)‖ * ‖ringComplex (primaryIdealGenerator q.2.2.1.val)‖ *
        ‖ringComplex (primaryIdealGenerator q.2.2.2.val)‖ ^ 3 := by
    rw [thetaFullFrequency, map_mul, map_mul, map_pow, norm_mul, norm_mul, norm_pow]
  rw [he]
  field_simp [hr, hI, hJ] <;> ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
