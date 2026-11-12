import GaloisForLFunctions.RHTower.Artin.ArtinElementarySubgroupOfARegularElement
import GaloisForLFunctions.RHTower.Artin.ArtinCongruenceModuloAPrime

/-!
# The class function of a `p`-regular element

Let `x` have order prime to `p` in a finite group `G`, `P` a `p`-subgroup of the centralizer of
`x` and `H = ⟨x⟩ · P ≅ ⟨x⟩ × P`. The function `ψ` on `H` with value `|⟨x⟩|` on `x · P` and `0`
elsewhere (`elementarySpike`) is the pullback of `|⟨x⟩| · 1_{x}` along the projection to `⟨x⟩`,
so it is a combination of linear characters of `H` with algebraic integer coefficients
(`elementarySpike_mem_virtualIntGroup`). Its induced function `ψ'` (`elementaryClassFunction`):

* lies in the span over the algebraic integers of the characters induced from any family that
  contains `H` (`elementaryClassFunction_mem_inducedSpanInt`);
* takes natural number values (`exists_nat_elementaryClassFunction`): it is a sum over the
  cosets of `H` of values of `ψ`;
* vanishes at the `p`-regular elements not conjugate to `x`
  (`elementaryClassFunction_eq_zero`), because a `p`-regular element of `x · P` is `x`;
* satisfies `|P| · ψ'(x) = |Z(x)|` (`card_mul_elementaryClassFunction_self`); for `P` a Sylow
  `p`-subgroup of the centralizer, `ψ'(x)` is its index, prime to `p`
  (`regularClassFunction_self`).
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### Combinations of linear characters -/

/-- A combination of linear characters is a combination of characters. -/
theorem linearIntSpan_le_virtualIntGroup (A : Type u) [Group A] :
    linearIntSpan A ≤ virtualIntGroup A := by
  rw [linearIntSpan, AddSubgroup.closure_le]
  rintro f ⟨a, ha, χ, rfl⟩
  exact AddSubgroup.subset_closure ⟨a, ha, _, linearCharacter_mem_fdCharacterSet χ, rfl⟩

/-- The pullback of a combination of linear characters along a homomorphism. -/
theorem comp_mem_linearIntSpan {A B : Type u} [Group A] [Group B] (π : B →* A) {f : A → ℂ}
    (hf : f ∈ linearIntSpan A) : (fun b => f (π b)) ∈ linearIntSpan B := by
  refine AddSubgroup.closure_induction
    (p := fun f _ => (fun b => f (π b)) ∈ linearIntSpan B) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨a, ha, χ, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, χ.comp π, rfl⟩
  · exact zero_mem _
  · intro u v _ _ hu hv
    exact add_mem hu hv
  · intro u _ hu
    exact neg_mem hu

/-- **A function on a finite abelian group with values in `|A|·𝓞` is an `𝓞`-combination of
linear characters**: its Fourier coefficients are algebraic integers. -/
theorem mem_linearIntSpan_of_card_mul {A : Type u} [CommGroup A] [Fintype A] (φ : A → ℂ)
    (hφ : ∀ c, ∃ a : ℂ, IsIntegral ℤ a ∧ φ c = (Nat.card A : ℂ) * a) :
    φ ∈ linearIntSpan A := by
  choose a ha hφa using hφ
  have hcard : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoeff : ∀ χ : LinearCharacter A,
      IsIntegral ℤ (characterPairing A (RHTower.deningerCharacterFn χ) φ) := by
    intro χ
    have e : characterPairing A (RHTower.deningerCharacterFn χ) φ =
        ∑ c : A, a c * RHTower.deningerCharacterFn χ c⁻¹ := by
      rw [characterPairing, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hφa c]
      field_simp
    rw [e]
    exact IsIntegral.sum _ fun c _ => (ha c).mul (isIntegral_linearCharacter χ c⁻¹)
  rw [← finiteAbelian_fourier_reconstruction φ]
  exact AddSubgroup.sum_mem _ fun χ _ =>
    AddSubgroup.subset_closure ⟨_, hcoeff χ, χ, funext fun c => rfl⟩

/-! ### Induction of combinations of characters -/

section Induction

variable {G : Type u} [Group G] [Fintype G]

/-- Induction of functions as an additive map. -/
def inducedFunctionHom (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) where
  toFun := inducedFunction H
  map_zero' := by
    have h := inducedFunction_smul H 0 (0 : H → ℂ)
    simp only [zero_mul] at h
    exact h
  map_add' := inducedFunction_add H

/-- **Induction maps the `𝓞`-span of the characters of a subgroup of the family into the
`𝓞`-span of the induced characters.** -/
theorem inducedFunction_mem_inducedSpanInt {𝔉 : Set (Subgroup G)} {H : Subgroup G}
    (hH : H ∈ 𝔉) {ψ : H → ℂ} (hψ : ψ ∈ virtualIntGroup H) :
    inducedFunction H ψ ∈ inducedSpanInt 𝔉 := by
  have hle : virtualIntGroup H ≤ (inducedSpanInt 𝔉).comap (inducedFunctionHom H) := by
    rw [virtualIntGroup, AddSubgroup.closure_le]
    rintro f ⟨a, ha, χ, hχ, rfl⟩
    show inducedFunction H (fun h => a * χ h) ∈ inducedSpanInt 𝔉
    rw [inducedFunction_smul]
    exact AddSubgroup.subset_closure ⟨a, ha, H, hH, χ, hχ, rfl⟩
  exact hle hψ

/-- The `𝓞`-span of the induced characters lies in the `𝓞`-span of the characters. -/
theorem inducedSpanInt_le_virtualIntGroup (𝔉 : Set (Subgroup G)) :
    inducedSpanInt 𝔉 ≤ virtualIntGroup G := by
  rw [inducedSpanInt, AddSubgroup.closure_le]
  rintro f ⟨a, ha, H, -, χ, hχ, rfl⟩
  exact AddSubgroup.subset_closure ⟨a, ha, _, inducedFunction_mem_fdCharacterSet H hχ, rfl⟩

end Induction

/-! ### The function on `⟨x⟩ · P` -/

section Spike

variable {G : Type u} [Group G] (x : G) (P : Subgroup G) (hP : P ≤ Subgroup.centralizer {x})
  {p : ℕ} (hx : (orderOf x).Coprime p) (hPp : IsPGroup p P)

/-- The function on `⟨x⟩ · P` with value `|⟨x⟩|` on `x · P` and `0` elsewhere. -/
def elementarySpike : elementarySubgroup x P hP → ℂ := fun h =>
  if ((elementaryEquiv x P hP hx hPp).symm h).1 = ⟨x, Subgroup.mem_zpowers x⟩ then
    (orderOf x : ℂ) else 0

theorem elementarySpike_apply (h : elementarySubgroup x P hP) :
    elementarySpike x P hP hx hPp h =
      if ((elementaryEquiv x P hP hx hPp).symm h).1 = ⟨x, Subgroup.mem_zpowers x⟩ then
        (orderOf x : ℂ) else 0 :=
  rfl

/-- The values of the extension by zero are natural numbers. -/
theorem exists_nat_extendByZero_elementarySpike (z : G) : ∃ n : ℕ,
    extendByZero (elementarySubgroup x P hP) (elementarySpike x P hP hx hPp) z = n := by
  by_cases hmem : z ∈ elementarySubgroup x P hP
  · rw [extendByZero_of_mem _ _ hmem, elementarySpike_apply]
    split_ifs
    · exact ⟨orderOf x, rfl⟩
    · exact ⟨0, Nat.cast_zero.symm⟩
  · exact ⟨0, by rw [extendByZero_of_notMem _ _ hmem, Nat.cast_zero]⟩

/-- **On the `p`-regular elements the extension by zero is `|⟨x⟩|` times the indicator of
`x`.** -/
theorem extendByZero_elementarySpike_of_regular {z : G} (hz : (orderOf z).Coprime p) :
    extendByZero (elementarySubgroup x P hP) (elementarySpike x P hP hx hPp) z =
      if z = x then (orderOf x : ℂ) else 0 := by
  by_cases hzx : z = x
  · rw [hzx, if_pos rfl, extendByZero_of_mem _ _ (mem_elementarySubgroup x P hP),
      elementarySpike_apply, if_pos (congrArg Prod.fst (elementaryEquiv_symm_self x P hP hx hPp))]
  · rw [if_neg hzx]
    by_cases hmem : z ∈ elementarySubgroup x P hP
    · rw [extendByZero_of_mem _ _ hmem, elementarySpike_apply, if_neg]
      exact fun hfst => hzx (eq_of_regular_of_fst_eq x P hP hx hPp hmem hz hfst)
    · exact extendByZero_of_notMem _ _ hmem

variable [Fintype G]

/-- **The function is a combination of linear characters of `⟨x⟩ · P` with algebraic integer
coefficients**: it is the pullback of `|⟨x⟩| · 1_{x}` along the projection to `⟨x⟩`. -/
theorem elementarySpike_mem_virtualIntGroup :
    elementarySpike x P hP hx hPp ∈ virtualIntGroup (elementarySubgroup x P hP) := by
  letI : CommGroup (Subgroup.zpowers x) := IsCyclic.commGroup
  have hδ : (fun c : Subgroup.zpowers x =>
      if c = ⟨x, Subgroup.mem_zpowers x⟩ then (orderOf x : ℂ) else 0) ∈
        linearIntSpan (Subgroup.zpowers x) := by
    refine mem_linearIntSpan_of_card_mul _ fun c => ?_
    rw [Nat.card_zpowers]
    by_cases hc : c = ⟨x, Subgroup.mem_zpowers x⟩
    · exact ⟨1, isIntegral_one, by rw [if_pos hc, mul_one]⟩
    · exact ⟨0, isIntegral_zero, by rw [if_neg hc, mul_zero]⟩
  exact linearIntSpan_le_virtualIntGroup _ (comp_mem_linearIntSpan
    ((MonoidHom.fst _ _).comp (elementaryEquiv x P hP hx hPp).symm.toMonoidHom) hδ)

/-! ### The induced class function -/

/-- The class function of `G` induced from the function on `⟨x⟩ · P`. -/
def elementaryClassFunction : G → ℂ :=
  inducedFunction (elementarySubgroup x P hP) (elementarySpike x P hP hx hPp)

theorem elementaryClassFunction_mem_inducedSpanInt {𝔉 : Set (Subgroup G)}
    (h𝔉 : elementarySubgroup x P hP ∈ 𝔉) :
    elementaryClassFunction x P hP hx hPp ∈ inducedSpanInt 𝔉 :=
  inducedFunction_mem_inducedSpanInt h𝔉 (elementarySpike_mem_virtualIntGroup x P hP hx hPp)

/-- **The values are natural numbers**: the induced function is the sum over the cosets of
`⟨x⟩ · P` of the values of the function at the conjugates by representatives. -/
theorem exists_nat_elementaryClassFunction (s : G) :
    ∃ n : ℕ, elementaryClassFunction x P hP hx hPp s = n := by
  have hclass := virtualIntGroup_conj (elementarySpike_mem_virtualIntGroup x P hP hx hPp)
  have hsum := sum_conj_eq_card_mul_sum_out (elementarySubgroup x P hP) _
    (extendByZero_conj _ hclass) s
  choose n hn using exists_nat_extendByZero_elementarySpike x P hP hx hPp
  refine ⟨∑ q : Quotient (QuotientGroup.rightRel (elementarySubgroup x P hP)),
    n (q.out * s * q.out⁻¹), ?_⟩
  have hcard : (Nat.card (elementarySubgroup x P hP) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [elementaryClassFunction, inducedFunction, hsum, ← mul_assoc, inv_mul_cancel₀ hcard,
    one_mul, Nat.cast_sum]
  exact Finset.sum_congr rfl fun q _ => hn _

/-- **The induced function vanishes at the `p`-regular elements not conjugate to `x`.** -/
theorem elementaryClassFunction_eq_zero {s : G} (hs : (orderOf s).Coprime p)
    (hconj : ∀ y : G, y * s * y⁻¹ ≠ x) : elementaryClassFunction x P hP hx hPp s = 0 := by
  rw [elementaryClassFunction, inducedFunction, Finset.sum_eq_zero, mul_zero]
  intro y _
  have hord : (orderOf (y * s * y⁻¹)).Coprime p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  rw [extendByZero_elementarySpike_of_regular x P hP hx hPp hord, if_neg (hconj y)]

/-- **At `x` the induced function is `|Z(x)| / |P|`.** -/
theorem card_mul_elementaryClassFunction_self :
    (Nat.card P : ℂ) * elementaryClassFunction x P hP hx hPp x =
      Nat.card (Subgroup.centralizer {x}) := by
  have hterm : ∀ y : G, extendByZero (elementarySubgroup x P hP)
      (elementarySpike x P hP hx hPp) (y * x * y⁻¹) =
        if y * x * y⁻¹ = x then (orderOf x : ℂ) else 0 := fun y =>
    extendByZero_elementarySpike_of_regular x P hP hx hPp (by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hx)
  -- the conjugations fixing `x` are the centralizer
  have hcount : (Finset.univ.filter fun y : G => y * x * y⁻¹ = x).card =
      Nat.card (Subgroup.centralizer {x}) := by
    rw [Nat.card_eq_fintype_card]
    refine (Fintype.card_of_subtype (p := fun y => y ∈ Subgroup.centralizer {x}) _ fun y => ?_).symm
    rw [Finset.mem_filter, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact and_iff_right (Finset.mem_univ y)
  have h1 : (orderOf x : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (orderOf_pos x).ne'
  have h2 : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [elementaryClassFunction, inducedFunction, Finset.sum_congr rfl fun y _ => hterm y,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount,
    card_elementarySubgroup x P hP hx hPp]
  push_cast
  field_simp

end Spike

/-! ### The Sylow subgroup of the centralizer -/

section Regular

variable {G : Type u} [Group G] [Fintype G] (p : ℕ) (x : G) (hx : (orderOf x).Coprime p)

/-- The class function of a `p`-regular element `x`: induced from `⟨x⟩ · P`, `P` a Sylow
`p`-subgroup of the centralizer of `x`. -/
def regularClassFunction : G → ℂ :=
  elementaryClassFunction x (centralizerSylow p x) (centralizerSylow_le p x) hx
    (centralizerSylow_isPGroup p x)

/-- It is a combination, with algebraic integer coefficients, of characters induced from
Brauer-elementary subgroups. -/
theorem regularClassFunction_mem_inducedSpanInt (hp : p.Prime) :
    regularClassFunction p x hx ∈ inducedSpanInt (brauerElementaryFamily G) :=
  elementaryClassFunction_mem_inducedSpanInt _ _ _ _ _
    (elementarySubgroup_mem_brauerElementaryFamily hp x _ _ hx (centralizerSylow_isPGroup p x))

theorem exists_nat_regularClassFunction (s : G) : ∃ n : ℕ, regularClassFunction p x hx s = n :=
  exists_nat_elementaryClassFunction _ _ _ _ _ s

theorem regularClassFunction_eq_zero {s : G} (hs : (orderOf s).Coprime p)
    (hconj : ∀ y : G, y * s * y⁻¹ ≠ x) : regularClassFunction p x hx s = 0 :=
  elementaryClassFunction_eq_zero _ _ _ _ _ hs hconj

/-- **At `x` the class function is the index of the Sylow subgroup in the centralizer**, a
number prime to `p` (`not_dvd_centralizerSylowIndex`). -/
theorem regularClassFunction_self :
    regularClassFunction p x hx x = centralizerSylowIndex p x := by
  have h := card_mul_elementaryClassFunction_self x (centralizerSylow p x)
    (centralizerSylow_le p x) hx (centralizerSylow_isPGroup p x)
  have h2 : (Nat.card (centralizerSylow p x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [card_centralizer_eq p x, Nat.cast_mul] at h
  exact mul_left_cancel₀ h2 h

end Regular

end GaloisForLFunctions
