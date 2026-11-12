import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheGramOfTwoRowsIsACompletedSum
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsAnAngularTwist

/-!
# The short sextic Gram is diagonal

For two coprime squarefree rows `u₁ = Π_{π ∈ s₁} π`, `u₂ = Π_{π ∈ s₂} π` (distinct primary primes
`π ∤ 6`, not both empty) the pair column `χ_{u₁}χ_{u₂}⁵` has mean zero on `O/(u₁u₂)`
(`sum_pairColumn_eq_zero`): at frequency `0` the mixed Gauss sum splits into
`g_{u₁}^{(1)}(0) g_{u₂}^{(5)}(0)`, and `g_c^{(j)}(0) = Σ_d χ_c(d)^j` vanishes for every nonempty
squarefree `c` and `6 ∤ j` (`sexticGaussPow_zero_prod`), since at a prime it is the sum of a
nontrivial character.

With the reflection of a column (`norm_tsum_eisensteinColumn_le`) the off-diagonal Gram entry of
two distinct rows is therefore bounded by `|det B|⁻¹ K (μ√(2/(3N(u₁u₂))))^{−M}` times the mean of the
dual coefficients (`norm_gramEntry_le`): for rows of norm `≍ U` and `N(u₁u₂) ≤ U^{1−ε}` it is
`O(U^{−A})` relative to the diagonal. Below the row scale the sextic mean square cancels completely
off the diagonal; a saving inside the mean square can only come from pairs with
`N(u₁u₂) ≥ U`, where the entry is the completed sum of `gramEntry_eq_completedSum`.
-/

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open HTGeometry HTGeometry.IntegerLatticePoisson MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates
  FamilyContinuationTheory

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Z" => Fin 2 → ℤ

/-! ### Gauss sums at frequency zero -/

/-- At a prime, `g_π^{(j)}(0) = Σ_d χ^j(d) = 0` for `6 ∤ j`. -/
theorem sexticGaussPow_zero_prime (π : O) [NeZero π] [(Ideal.span {π}).IsMaximal]
    (hlam : lambda ∉ Ideal.span {π}) (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : ¬ 6 ∣ j) : sexticGaussPow j π 0 = 0 := by
  have hχ : complexSexticChar (Ideal.span {π}) hlam ^ j ≠ 1 := fun h =>
    hj6 ((complexSexticChar_pow_eq_one_iff π hlam h2 j).mp h)
  have hres : ∀ d : O ⧸ Ideal.span {π},
      sexticResidue π d ^ j = (complexSexticChar (Ideal.span {π}) hlam ^ j) d := by
    intro d
    unfold sexticResidue
    rw [sexticSymbol_prime π hlam h2 hprim, mk_qrep, MulChar.pow_apply' _ hj0]
  unfold sexticGaussPow
  simp only [map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one, hres]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- For a nonempty squarefree product of distinct primary primes, `g_c^{(j)}(0) = 0`, `6 ∤ j`. -/
theorem sexticGaussPow_zero_prod (s : Finset O) (hs : s.Nonempty) (hnz : ∀ π ∈ s, π ≠ 0)
    (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
    (hcop : (s : Set O).Pairwise IsCoprime) [hne : NeZero (∏ π ∈ s, π)]
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : ¬ 6 ∣ j) : sexticGaussPow j (∏ π ∈ s, π) 0 = 0 := by
  obtain ⟨π, hπ⟩ := hs
  have he : ∏ x ∈ s, x = π * ∏ x ∈ s.erase π, x := (Finset.mul_prod_erase s _ hπ).symm
  haveI : (Ideal.span {π}).IsMaximal := hmax π hπ
  haveI : NeZero π := ⟨hnz π hπ⟩
  have ht0 : ∏ x ∈ s.erase π, x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x hx => hnz x (Finset.mem_of_mem_erase hx)
  haveI : NeZero (∏ x ∈ s.erase π, x) := ⟨ht0⟩
  haveI : NeZero (π * ∏ x ∈ s.erase π, x) := ⟨mul_ne_zero (hnz π hπ) ht0⟩
  have hcopπ : IsCoprime π (∏ x ∈ s.erase π, x) :=
    IsCoprime.prod_right fun x hx =>
      hcop hπ (Finset.mem_of_mem_erase hx) (fun h => (Finset.ne_of_mem_erase hx) h.symm)
  have hcong : sexticGaussPow j (∏ x ∈ s, x) 0 = sexticGaussPow j (π * ∏ x ∈ s.erase π, x) 0 := by
    have : ∀ {c c' : O} [NeZero c] [NeZero c'], c = c' →
        sexticGaussPow j c 0 = sexticGaussPow j c' 0 := by
      intro c c' _ _ h
      subst h
      rfl
    exact this he
  rw [hcong, sexticGaussPow_mul j π _ hcopπ 0,
    sexticGaussPow_zero_prime π (hlam π hπ) (h2 π hπ) (hprim π hπ) hj0 hj6, mul_zero, zero_mul]

/-! ### Distinct rows are orthogonal -/

/-- **The pair column of two distinct squarefree rows has mean zero.** -/
theorem sum_pairColumn_eq_zero (s₁ s₂ : Finset O) (hdisj : Disjoint s₁ s₂)
    (hne12 : (s₁ ∪ s₂).Nonempty) (hnz : ∀ π ∈ s₁ ∪ s₂, π ≠ 0)
    (hmax : ∀ π ∈ s₁ ∪ s₂, (Ideal.span {π}).IsMaximal)
    (hlam : ∀ π ∈ s₁ ∪ s₂, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s₁ ∪ s₂, (2 : O) ∉ Ideal.span {π})
    (hprim : ∀ π ∈ s₁ ∪ s₂, lambda ^ 2 ∣ π - 1)
    (hcop : ((s₁ ∪ s₂ : Finset O) : Set O).Pairwise IsCoprime)
    [NeZero (∏ π ∈ s₁, π)] [NeZero (∏ π ∈ s₂, π)] :
    ∑ m : O ⧸ Ideal.span {(∏ π ∈ s₁, π) * ∏ π ∈ s₂, π},
      pairColumn 1 5 (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) m = 0 := by
  have hsub1 : s₁ ⊆ s₁ ∪ s₂ := Finset.subset_union_left
  have hsub2 : s₂ ⊆ s₁ ∪ s₂ := Finset.subset_union_right
  have hcop12 : IsCoprime (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) :=
    IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy =>
      hcop (hsub1 hx) (hsub2 hy) (fun h => Finset.disjoint_left.mp hdisj hx (h ▸ hy))
  have hsplit := sum_pairColumn_traceChar 1 5 (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) hcop12 0
  simp only [map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one] at hsplit
  rw [hsplit]
  rcases Finset.Nonempty.exists_mem hne12 with ⟨π, hπ⟩
  rcases Finset.mem_union.mp hπ with h1 | h2'
  · rw [sexticGaussPow_zero_prod s₁ ⟨π, h1⟩ (fun x hx => hnz x (hsub1 hx))
      (fun x hx => hmax x (hsub1 hx)) (fun x hx => hlam x (hsub1 hx))
      (fun x hx => h2 x (hsub1 hx)) (fun x hx => hprim x (hsub1 hx))
      (hcop.mono (by intro x hx; exact hsub1 hx)) one_ne_zero (by norm_num)]
    ring
  · rw [sexticGaussPow_zero_prod s₂ ⟨π, h2'⟩ (fun x hx => hnz x (hsub2 hx))
      (fun x hx => hmax x (hsub2 hx)) (fun x hx => hlam x (hsub2 hx))
      (fun x hx => h2 x (hsub2 hx)) (fun x hx => hprim x (hsub2 hx))
      (hcop.mono (by intro x hx; exact hsub2 hx)) (by norm_num) (by norm_num)]
    ring

/-- The pair column of `u₁, u₂` read on `O/(a + bω)` when `a + bω = u₁u₂`. -/
def pairColumnAt (u₁ u₂ : O) (a b : ℤ) (hab : eval a b = u₁ * u₂)
    (d : O ⧸ Ideal.span {eval a b}) : ℂ :=
  pairColumn 1 5 u₁ u₂ (Ideal.Quotient.factor (le_of_eq (congrArg (fun x => Ideal.span {x}) hab)) d)

/-- **The short sextic Gram is diagonal.** For two distinct coprime squarefree rows
`u₁ = Π_{s₁} π`, `u₂ = Π_{s₂} π` with `u₁u₂ = a + bω`, rows weighted by `f(Bn)`,
`‖B^{−*}v‖ ≥ μ‖v‖` and `M > 2`, the off-diagonal Gram entry
`Σ_n χ_{u₁}(n)χ_{u₂}(n)⁵ f(Bn)` is at most `|det B|⁻¹ K (μ√(2/(3N)))^{−M}` times the mean of the
dual coefficients, `N = N(u₁u₂)`. -/
theorem norm_gramEntry_le (f : SchwartzMap E ℂ) {M : ℕ} (hM : (2 : ℝ) < M) (B : E ≃L[ℝ] E)
    {μ : ℝ} (hμ : 0 < μ) (hT : ∀ v, μ * ‖v‖ ≤ ‖inverseAdjoint B v‖)
    (s₁ s₂ : Finset O) (hdisj : Disjoint s₁ s₂)
    (hne12 : (s₁ ∪ s₂).Nonempty) (hnz : ∀ π ∈ s₁ ∪ s₂, π ≠ 0)
    (hmax : ∀ π ∈ s₁ ∪ s₂, (Ideal.span {π}).IsMaximal)
    (hlam : ∀ π ∈ s₁ ∪ s₂, lambda ∉ Ideal.span {π})
    (h2 : ∀ π ∈ s₁ ∪ s₂, (2 : O) ∉ Ideal.span {π})
    (hprim : ∀ π ∈ s₁ ∪ s₂, lambda ^ 2 ∣ π - 1)
    (hcop : ((s₁ ∪ s₂ : Finset O) : Set O).Pairwise IsCoprime)
    [NeZero (∏ π ∈ s₁, π)] [NeZero (∏ π ∈ s₂, π)] (a b : ℤ)
    (hab : eval a b = (∏ π ∈ s₁, π) * ∏ π ∈ s₂, π) [hc : NeZero (eval a b)] :
    ‖∑' n : Z, (sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₁, π) *
        sexticSymbol (eval (n 0) (n 1)) (∏ π ∈ s₂, π) ^ 5) * f (B (euclideanIntegerPoint n))‖ ≤
      latticeScale B * ((SchwartzMap.seminorm ℝ M 0 (𝓕 f) * (3 * 2 + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) *
          (μ * Real.sqrt (2 / (3 * (eisNormZ a b : ℝ)))) ^ (-(M : ℝ))) *
        ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℝ)⁻¹ *
          ∑ h : O ⧸ Ideal.span {eval a b},
            ‖dualCoeff a b (pairColumnAt (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) a b hab) h‖) := by
  set φ := pairColumnAt (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) a b hab
  have hφ : ∀ x : O, φ (Ideal.Quotient.mk _ x) =
      sexticSymbol x (∏ π ∈ s₁, π) * sexticSymbol x (∏ π ∈ s₂, π) ^ 5 := by
    intro x
    simp only [φ, pairColumnAt, Ideal.Quotient.factor_mk, pairColumn_mk, pow_one]
  have hmean : ∑ d, φ d = 0 := by
    have hbij : Function.Bijective (Ideal.Quotient.factor
        (le_of_eq (congrArg (fun x => Ideal.span {x}) hab))) := by
      refine ⟨fun x y hxy => ?_, fun y => ?_⟩
      · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at hxy
        rw [Ideal.Quotient.eq, hab]
        exact hxy
      · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ y, Ideal.Quotient.factor_mk _ _⟩
    have := Fintype.sum_bijective _ hbij (fun d => φ d)
      (fun m => pairColumn 1 5 (∏ π ∈ s₁, π) (∏ π ∈ s₂, π) m) (fun _ => rfl)
    rw [this]
    exact sum_pairColumn_eq_zero s₁ s₂ hdisj hne12 hnz hmax hlam h2 hprim hcop
  have h := norm_tsum_eisensteinColumn_le f hM B hμ hT a b φ hmean
  simp_rw [hφ] at h
  exact h

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
