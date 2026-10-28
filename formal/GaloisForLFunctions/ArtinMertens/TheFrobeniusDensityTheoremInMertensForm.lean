import GaloisForLFunctions.ArtinMertens.ThePermutationCharactersSatisfyMertens

/-!
# Artin induction and the Frobenius density theorem in Mertens form

Let `G` be a Galois group of a number field `L` over `ℚ`. A function `φ : G → ℝ` is
**division-constant** if `φ(h) = φ(g)` whenever `⟨h⟩` is conjugate to `⟨g⟩`; the characters of
representations over `ℚ` are of this kind. For every such `φ` and every choice of Frobenius elements,
`Σ_{p ≤ x, p ∤ disc L} φ(Frob_p) log p/p = ⟨φ, 1⟩ log x + o(log x)`, `⟨φ, 1⟩ = |G|⁻¹ Σ_σ φ(σ)`
(`tendsto_frobMertens_div_log`). For the indicator of a division `Δ` this is the Frobenius density
theorem in Mertens form: `Σ_{Frob_p ∈ Δ} log p/p ∼ (|Δ|/|G|) log x`
(`tendsto_frobMertens_divisionIndicator_div_log`).

* **Burnside** (`classMean_permChar`): `⟨π_H, 1⟩ = 1`.
* **Mertens on the span** (`tendsto_frobMertens_div_log_of_mem`): the Mertens sums are linear in
  `φ`, so permutation-character Mertens (`tendsto_frobMertens_permChar_div_log`) passes to
  `span_ℝ {π_H}`.
* **Artin induction** (`mem_permSpan_of_isDivisionConstant`): with `A f(g) = |G|⁻¹ Σ_x f(x⁻¹gx)`,
  `A 1_C = (|C|/|G|) π_C`, and `1_C = e_C + Σ_{C' < C cyclic} e_{C'}` where `e_C(g) = [⟨g⟩ = C]`;
  strong induction on `|C|` puts every `A e_C` in the span, and a division-constant `φ` is
  `A φ = Σ_C φ(C) A e_C`.
-/

noncomputable section

open NumberField Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.ArtinMertens

section Induction

variable {G : Type*} [Group G] [Fintype G]

/-- The **mean** `⟨φ, 1⟩ = |G|⁻¹ Σ_σ φ(σ)`. -/
def classMean (φ : G → ℝ) : ℝ := (Fintype.card G : ℝ)⁻¹ * ∑ σ, φ σ

omit [Group G] in
theorem classMean_add (φ ψ : G → ℝ) : classMean (φ + ψ) = classMean φ + classMean ψ := by
  simp only [classMean, Pi.add_apply, sum_add_distrib, mul_add]

omit [Group G] in
theorem classMean_smul (c : ℝ) (φ : G → ℝ) : classMean (c • φ) = c * classMean φ := by
  simp only [classMean, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  ring

/-- For fixed `g`, `#{σ : g⁻¹σg ∈ H} = |H|`. -/
theorem sum_conj_mem (H : Subgroup G) (g : G) :
    ∑ σ : G, (if g⁻¹ * σ * g ∈ H then (1 : ℝ) else 0) = Nat.card H := by
  rw [← Equiv.sum_comp (MulAut.conj g).toEquiv]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, mul_assoc,
    inv_mul_cancel_left, inv_mul_cancel, mul_one, sum_boole]
  rw [← Nat.card_eq_finsetCard]
  exact congrArg Nat.cast (Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp))

/-- **Burnside**: `⟨π_H, 1⟩ = 1`. -/
theorem classMean_permChar (H : Subgroup G) : classMean (permChar H) = 1 := by
  have hH : (0 : ℝ) < Nat.card H := by exact_mod_cast Nat.card_pos
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have key : ∑ σ : G, ((univ.filter fun g : G => g⁻¹ * σ * g ∈ H).card : ℝ) =
      Fintype.card G * Nat.card H := by
    simp_rw [card_filter]
    push_cast
    rw [sum_comm]
    simp_rw [sum_conj_mem H]
    simp
  simp only [classMean, permChar]
  rw [← sum_div, key]
  field_simp

/-- The **conjugation average** `(A f)(g) = |G|⁻¹ Σ_x f(x⁻¹gx)`. -/
def conjAvg : (G → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun f g := (Fintype.card G : ℝ)⁻¹ * ∑ x : G, f (x⁻¹ * g * x)
  map_add' f f' := by
    ext g
    simp only [Pi.add_apply, sum_add_distrib, mul_add]
  map_smul' c f := by
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ => by ring

theorem conjAvg_apply (f : G → ℝ) (g : G) :
    conjAvg f g = (Fintype.card G : ℝ)⁻¹ * ∑ x : G, f (x⁻¹ * g * x) := rfl

/-- The indicator `1_C` of a subgroup. -/
def subgroupIndicator (C : Subgroup G) (g : G) : ℝ := if g ∈ C then 1 else 0

/-- The **generator indicator** `e_C(g) = [⟨g⟩ = C]`. -/
def generatorIndicator (C : Subgroup G) (g : G) : ℝ := if Subgroup.zpowers g = C then 1 else 0

/-- The cyclic subgroups of `G`. -/
def cyclicSubgroups (G : Type*) [Group G] [Fintype G] : Finset (Subgroup G) :=
  univ.image Subgroup.zpowers

variable (G) in
/-- The span `span_ℝ {π_H : H ≤ G}` of the permutation characters. -/
def permSpan : Submodule ℝ (G → ℝ) := Submodule.span ℝ (Set.range fun H : Subgroup G => permChar H)

/-- `A 1_C = (|C|/|G|) π_C`. -/
theorem conjAvg_subgroupIndicator (C : Subgroup G) :
    conjAvg (subgroupIndicator C) = ((Nat.card C : ℝ) / Fintype.card G) • permChar C := by
  have hC : (0 : ℝ) < Nat.card C := by exact_mod_cast Nat.card_pos
  ext g
  simp only [conjAvg_apply, subgroupIndicator, sum_boole, Pi.smul_apply, smul_eq_mul, permChar]
  field_simp

/-- `1_C = e_C + Σ_{C' < C cyclic} e_{C'}`: each `g ∈ C` generates exactly one cyclic `⟨g⟩ ≤ C`. -/
theorem subgroupIndicator_eq (C : Subgroup G) :
    subgroupIndicator C = generatorIndicator C +
      ∑ C' ∈ (cyclicSubgroups G).filter (· < C), generatorIndicator C' := by
  ext g
  rw [Pi.add_apply, Finset.sum_apply]
  simp only [subgroupIndicator, generatorIndicator, sum_ite_eq, mem_filter, cyclicSubgroups,
    mem_image, mem_univ, true_and, exists_apply_eq_apply]
  rw [← Subgroup.zpowers_le]
  by_cases h1 : Subgroup.zpowers g = C
  · simp [h1]
  · by_cases h2 : Subgroup.zpowers g < C
    · simp [h1, h2, h2.le]
    · have h3 : ¬ Subgroup.zpowers g ≤ C := fun h => h2 (lt_of_le_of_ne h h1)
      simp [h1, h2, h3]

theorem card_lt_of_lt {C' C : Subgroup G} (h : C' < C) : Nat.card C' < Nat.card C :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

/-- Every averaged generator indicator `A e_C` lies in the span of the permutation characters. -/
theorem conjAvg_generatorIndicator_mem (C : Subgroup G) :
    conjAvg (generatorIndicator C) ∈ permSpan G := by
  suffices h : ∀ n, ∀ C : Subgroup G, Nat.card C = n →
      conjAvg (generatorIndicator C) ∈ permSpan G from h _ C rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hC
  have hA : conjAvg (generatorIndicator C) = conjAvg (subgroupIndicator C) -
      ∑ C' ∈ (cyclicSubgroups G).filter (· < C), conjAvg (generatorIndicator C') := by
    rw [subgroupIndicator_eq C, map_add, map_sum]
    abel
  rw [hA]
  refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun C' hC' => ?_)
  · rw [conjAvg_subgroupIndicator]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨C, rfl⟩)
  · exact ih _ (hC ▸ card_lt_of_lt (mem_filter.mp hC').2) C' rfl

/-- `φ` is **division-constant**: `φ(h) = φ(g)` whenever `⟨h⟩` is conjugate to `⟨g⟩`. -/
def IsDivisionConstant (φ : G → ℝ) : Prop :=
  ∀ g h x : G, Subgroup.zpowers h = Subgroup.zpowers (x * g * x⁻¹) → φ h = φ g

/-- The value of `φ` at a generator of `C` (zero if `C` is not cyclic). -/
def divisionValue (φ : G → ℝ) (C : Subgroup G) : ℝ :=
  if h : ∃ g, Subgroup.zpowers g = C then φ h.choose else 0

/-- **Artin induction**: a division-constant function lies in `span_ℝ {π_H}`. -/
theorem mem_permSpan_of_isDivisionConstant {φ : G → ℝ} (hφ : IsDivisionConstant φ) :
    φ ∈ permSpan G := by
  -- `φ` is a class function, so `A φ = φ`
  have hconj : conjAvg φ = φ := by
    ext g
    have hx : ∀ x : G, φ (x⁻¹ * g * x) = φ g := fun x => hφ g _ x⁻¹ (by rw [inv_inv])
    have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    simp only [conjAvg_apply, hx, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  -- `φ = Σ_C φ(C) e_C`
  have hdecomp : φ = ∑ C ∈ cyclicSubgroups G, divisionValue φ C • generatorIndicator C := by
    ext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, generatorIndicator, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq, if_pos (show Subgroup.zpowers g ∈ cyclicSubgroups G from
      mem_image_of_mem _ (mem_univ g))]
    have h : ∃ a, Subgroup.zpowers a = Subgroup.zpowers g := ⟨g, rfl⟩
    rw [divisionValue, dif_pos h]
    exact (hφ g h.choose 1 (by rw [h.choose_spec, one_mul, inv_one, mul_one])).symm
  rw [← hconj, hdecomp, map_sum]
  exact Submodule.sum_mem _ fun C _ => by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (conjAvg_generatorIndicator_mem C)

omit [Fintype G] in
theorem zpowers_conj_eq {g k : G} (h : Subgroup.zpowers g = Subgroup.zpowers k) (x : G) :
    Subgroup.zpowers (x * g * x⁻¹) = Subgroup.zpowers (x * k * x⁻¹) := by
  have := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) h
  simpa [MonoidHom.map_zpowers] using this

/-- The indicator of the **division** of `g₀`: the elements generating a conjugate of `⟨g₀⟩`. -/
def divisionIndicator (g₀ g : G) : ℝ :=
  if ∃ x : G, Subgroup.zpowers g = Subgroup.zpowers (x * g₀ * x⁻¹) then 1 else 0

theorem isDivisionConstant_divisionIndicator (g₀ : G) :
    IsDivisionConstant (divisionIndicator g₀) := by
  intro g h x hx
  have hiff : (∃ y : G, Subgroup.zpowers h = Subgroup.zpowers (y * g₀ * y⁻¹)) ↔
      ∃ y : G, Subgroup.zpowers g = Subgroup.zpowers (y * g₀ * y⁻¹) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨x⁻¹ * y, ?_⟩
      have h1 := zpowers_conj_eq (hx.symm.trans hy) x⁻¹
      simpa [mul_assoc] using h1
    · rintro ⟨y, hy⟩
      refine ⟨x * y, ?_⟩
      rw [hx, zpowers_conj_eq hy x]
      simp [mul_assoc]
  simp only [divisionIndicator, hiff]

end Induction

section Mertens

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G ℚ L]

omit [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L] in
theorem frobMertens_add (frob : ℕ → G) (φ ψ : G → ℝ) (x : ℕ) :
    frobMertens L frob (φ + ψ) x = frobMertens L frob φ x + frobMertens L frob ψ x := by
  simp only [frobMertens, Pi.add_apply, add_mul, sum_add_distrib]

omit [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L] in
theorem frobMertens_smul (frob : ℕ → G) (c : ℝ) (φ : G → ℝ) (x : ℕ) :
    frobMertens L frob (c • φ) x = c * frobMertens L frob φ x := by
  simp only [frobMertens, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

/-- **Mertens on the span of the permutation characters**. -/
theorem tendsto_frobMertens_div_log_of_mem {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {φ : G → ℝ} (hφ : φ ∈ permSpan G) :
    Tendsto (fun x : ℕ => frobMertens L frob φ x / Real.log x) atTop (𝓝 (classMean φ)) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨H, rfl⟩ := hφ
    rw [classMean_permChar]
    exact tendsto_frobMertens_permChar_div_log hfrob H
  | zero =>
    have h0 : classMean (0 : G → ℝ) = 0 := by simp [classMean]
    rw [h0]
    refine tendsto_const_nhds.congr fun x => ?_
    simp [frobMertens]
  | add φ ψ _ _ hφ hψ =>
    rw [classMean_add]
    refine (hφ.add hψ).congr fun x => ?_
    rw [frobMertens_add, add_div]
  | smul c φ _ hφ =>
    rw [classMean_smul]
    refine (hφ.const_mul c).congr fun x => ?_
    rw [frobMertens_smul, mul_div_assoc]

/-- **Mertens' theorem for division-constant class functions**: for every choice of Frobenius
elements, `Σ_{p ≤ x, p ∤ disc L} φ(Frob_p) log p/p ∼ ⟨φ, 1⟩ log x`. -/
theorem tendsto_frobMertens_div_log {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {φ : G → ℝ} (hφ : IsDivisionConstant φ) :
    Tendsto (fun x : ℕ => frobMertens L frob φ x / Real.log x) atTop (𝓝 (classMean φ)) :=
  tendsto_frobMertens_div_log_of_mem hfrob (mem_permSpan_of_isDivisionConstant hφ)

/-- **The Frobenius density theorem in Mertens form**: the primes whose Frobenius lies in the
division `Δ` of `g₀` satisfy `Σ_{Frob_p ∈ Δ} log p/p ∼ (|Δ|/|G|) log x`. -/
theorem tendsto_frobMertens_divisionIndicator_div_log {frob : ℕ → G}
    (hfrob : IsFrobeniusChoice L frob) (g₀ : G) :
    Tendsto (fun x : ℕ => frobMertens L frob (divisionIndicator g₀) x / Real.log x) atTop
      (𝓝 (classMean (divisionIndicator g₀))) :=
  tendsto_frobMertens_div_log hfrob (isDivisionConstant_divisionIndicator g₀)

end Mertens

end GaloisForLFunctions.ArtinMertens
