import GaloisForLFunctions.HTGeometry.RittLevelOneClassification
import GaloisForLFunctions.HTGeometry.RittTowerDescentStep

/-!
# The classification at jet order two

The second jet prefix field is `K⟮τ⟯⟮dτ⟯`, and the shift scales both generators: `σ τ = q·τ` and
`σ(dτ) = (q/ρ)·dτ`.  So the scaling classification applies twice, first over the coefficient field
`K⟮τ⟯` and then over `K` itself, and the two passes compose:

* the first pass splits off a pure power relation in `K⟮τ⟯` with scalar `(q/ρ)^s`, or an affine
  relation whose inhomogeneity is one of the two components of the original one, or writes
  `V = u·(dτ)^j` with the inhomogeneity gone;
* the second pass does the same over `K`, and its monomial alternative needs the inhomogeneity to
  vanish, which the affine branch of the first pass forbids.

Composing, a pure power at the first pass has `ρ`-exponent `−s ≠ 0` and therefore always yields
Ritt's order-one form; an affine first pass always yields a base relation with nonzero
inhomogeneity; and only the monomial-then-monomial route survives, giving

`V = κ·τ^{e₀}·(dτ)^{e₁}`,  `κ` shift-fixed,  `c = q^{e₀+e₁}·ρ^{−e₁}`,  inhomogeneity zero.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The classification at jet order two.** -/
theorem level_two_classification (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c α β₀ g : K} (hc : c ≠ 0) {i k : ℤ} (hcik : c = q ^ i * Fr.ρ ^ k)
    (hrel : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L α * Fr.d τ + (algebraMap K L β₀ * τ + algebraMap K L g))) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (¬(α = 0 ∧ β₀ = 0 ∧ g = 0) ∧
      ∃ (u c' h : K), u ≠ 0 ∧ c' ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = c' * u + h) ∨
    (∃ (κ : K) (e₀ e₁ : ℤ), κ ≠ 0 ∧ Fr.ψ κ = κ ∧ α = 0 ∧ β₀ = 0 ∧ g = 0 ∧
      V = algebraMap K L κ * τ ^ e₀ * (Fr.d τ) ^ e₁ ∧ i = e₀ + e₁ ∧ k = -e₁) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set E : IntermediateField K L := Fr.jetPrefixField τ 1 with hEdef
  have hEσ : ∀ x ∈ E, Fr.σ x ∈ E := Fr.sigma_mem_jetPrefixField hqconst hshift 1
  set φ : ↥E →+* ↥E :=
    { toFun := fun x => ⟨Fr.σ (x : L), hEσ (x : L) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ
  have hcompE : ∀ x : ↥E, Fr.σ (algebraMap ↥E L x) = algebraMap ↥E L (φ x) := fun _ => rfl
  set aK : K := q / Fr.ρ with haKdef
  have haK0 : aK ≠ 0 := div_ne_zero hq hρ0
  set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
  have haE0 : aE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
  set cE : ↥E := ⟨algebraMap K L c, IntermediateField.algebraMap_mem _ _⟩ with hcE
  have hcE0 : cE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc) (congrArg Subtype.val h)
  set αE : ↥E := ⟨algebraMap K L α, IntermediateField.algebraMap_mem _ _⟩ with hαE
  have hτmem : τ ∈ E := by
    have h0 := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 1) (by omega)
    simpa using h0
  have hβmem : algebraMap K L β₀ * τ + algebraMap K L g ∈ E :=
    add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hτmem)
      (IntermediateField.algebraMap_mem _ _)
  set βE : ↥E := ⟨algebraMap K L β₀ * τ + algebraMap K L g, hβmem⟩ with hβE
  have hσt : Fr.σ (Fr.d τ) = algebraMap ↥E L aE * Fr.d τ :=
    Fr.sigma_d_eq_of_shift hqconst hshift
  have hVadj : V ∈ IntermediateField.adjoin ↥E ({Fr.d τ} : Set L) := by
    have hV2 : V ∈ Fr.jetPrefixField τ (1 + 1) := hV
    have := (jetPrefixField_succ_eq Fr τ 1) ▸ hV2
    exact this
  have hrelE : Fr.σ V = algebraMap ↥E L cE * V
      + (algebraMap ↥E L αE * Fr.d τ + algebraMap ↥E L βE) := hrel
  have hcoez : ∀ (x : ↥E) (n : ℤ), ((x ^ n : ↥E) : L) = ((x : L)) ^ n :=
    fun x n => map_zpow₀ (algebraMap ↥E L) x n
  rcases scaling_dichotomy_of_mem_adjoin (E := ↥E) Fr.σ φ hcompE htr1 haE0 hcE0 hσt hV0 hVadj
      hrelE with ⟨w, s, hw0, hs0, hweq⟩ | ⟨w, s, h, hw0, hh0, hhsrc, hweq⟩ |
      ⟨u, j, hu0, hα0, hβ0, hVeq, hueq⟩
  · -- a pure power relation over `K⟮τ⟯`
    have hwL : (w : L) ≠ 0 := fun hh => hw0 (Subtype.ext (by simpa using hh))
    have hcast := congrArg (fun z : ↥E => (z : L)) hweq
    simp only [hφ] at hcast
    push_cast [hcoez] at hcast
    simp only [haE] at hcast
    have e1 : algebraMap K L (aK ^ s) = (algebraMap K L aK) ^ s := map_zpow₀ _ _ _
    have hrel1 : Fr.σ (w : L) = algebraMap K L (aK ^ s) * (w : L)
        + (algebraMap K L 0 * τ + algebraMap K L 0) := by
      rw [e1, map_zero, zero_mul, add_zero, add_zero]
      linear_combination hcast
    have hak0 : aK ^ s ≠ 0 := zpow_ne_zero _ haK0
    rcases level_one_classification Fr hq hshift htr0 hwL w.2 hak0 hrel1 with
        ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', hw'0, hh'0, hh'src, hw'eq⟩ |
        ⟨u', j', hu'0, -, -, -, hu'eq⟩
    · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
    · exact absurd (by rcases hh'src with hh | hh <;> rw [hh] <;> simp) hh'0
    · refine Or.inl ⟨u', -j' + s, -s, hu'0, ?_, ?_⟩
      · rintro ⟨-, hh⟩
        exact hs0 (by omega)
      · have hmul : q ^ (-j') * aK ^ s = q ^ (-j' + s) * Fr.ρ ^ (-s) := by
          rw [haKdef, div_zpow, zpow_add₀ hq, zpow_neg Fr.ρ s, div_eq_mul_inv]
          ring
        rw [hu'eq, hmul]
  · -- an affine relation over `K⟮τ⟯`
    have hwL : (w : L) ≠ 0 := fun hh => hw0 (Subtype.ext (by simpa using hh))
    have hc1 : aK ^ s * c ≠ 0 := mul_ne_zero (zpow_ne_zero _ haK0) hc
    rcases hhsrc with rfl | rfl
    · have hcast := congrArg (fun z : ↥E => (z : L)) hweq
      simp only [hφ] at hcast
      push_cast [hcoez] at hcast
      simp only [haE, hcE, hβE] at hcast
      have e1 : algebraMap K L (aK ^ s * c)
          = (algebraMap K L aK) ^ s * algebraMap K L c := by rw [map_mul, map_zpow₀]
      have hrel1 : Fr.σ (w : L) = algebraMap K L (aK ^ s * c) * (w : L)
          + (algebraMap K L β₀ * τ + algebraMap K L g) := by
        rw [e1]
        linear_combination hcast
      have hβne : ¬ (β₀ = 0 ∧ g = 0) := by
        rintro ⟨hb, hg⟩
        refine hh0 (Subtype.ext ?_)
        show algebraMap K L β₀ * τ + algebraMap K L g = ((0 : ↥E) : L)
        rw [hb, hg, map_zero, zero_mul, add_zero]
        rfl
      rcases level_one_classification Fr hq hshift htr0 hwL w.2 hc1 hrel1 with
          ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', hw'0, hh'0, -, hw'eq⟩ |
          ⟨u', j', hu'0, hb0, hg0, -, -⟩
      · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
      · exact Or.inr (Or.inl ⟨by rintro ⟨-, hb, hg⟩; exact hβne ⟨hb, hg⟩,
          w', q ^ s' * (aK ^ s * c), h', hw'0,
          mul_ne_zero (zpow_ne_zero _ hq) hc1, hh'0, hw'eq⟩)
      · exact absurd ⟨hb0, hg0⟩ hβne
    · have hαne : α ≠ 0 := by
        intro hzero
        refine hh0 ?_
        have hα0' : αE = 0 := by
          refine Subtype.ext ?_
          show algebraMap K L α = ((0 : ↥E) : L)
          rw [hzero, map_zero]
          rfl
        rw [hα0', zero_div]
      have hcast := congrArg (fun z : ↥E => (z : L)) hweq
      simp only [hφ] at hcast
      push_cast [hcoez] at hcast
      simp only [haE, hcE, hαE] at hcast
      have e1 : algebraMap K L (aK ^ s * c)
          = (algebraMap K L aK) ^ s * algebraMap K L c := by rw [map_mul, map_zpow₀]
      have e2 : algebraMap K L (α / aK)
          = algebraMap K L α / algebraMap K L aK := map_div₀ _ _ _
      have hrel1 : Fr.σ (w : L) = algebraMap K L (aK ^ s * c) * (w : L)
          + (algebraMap K L 0 * τ + algebraMap K L (α / aK)) := by
        rw [e1, e2, map_zero, zero_mul, zero_add]
        linear_combination hcast
      rcases level_one_classification Fr hq hshift htr0 hwL w.2 hc1 hrel1 with
          ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', hw'0, hh'0, -, hw'eq⟩ |
          ⟨u', j', hu'0, -, hg0, -, -⟩
      · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
      · exact Or.inr (Or.inl ⟨by rintro ⟨ha, -, -⟩; exact hαne ha,
          w', q ^ s' * (aK ^ s * c), h', hw'0,
          mul_ne_zero (zpow_ne_zero _ hq) hc1, hh'0, hw'eq⟩)
      · exact absurd hg0 (div_ne_zero hαne haK0)
  · -- a monomial over `K⟮τ⟯`
    have huL : (u : L) ≠ 0 := fun hh => hu0 (Subtype.ext (by simpa using hh))
    have hαzero : α = 0 := by
      have hh := congrArg (fun z : ↥E => (z : L)) hα0
      simp only [hαE] at hh
      exact (algebraMap K L).injective (by simpa using hh)
    have hβzero : β₀ = 0 ∧ g = 0 := by
      have hb := congrArg (fun z : ↥E => (z : L)) hβ0
      simp only [hβE] at hb
      have hb' : algebraMap K L β₀ * τ + algebraMap K L g = 0 := by simpa using hb
      by_cases hb0 : β₀ = 0
      · refine ⟨hb0, ?_⟩
        rw [hb0, map_zero, zero_mul, zero_add] at hb'
        exact (algebraMap K L).injective (by rw [hb', map_zero])
      · exfalso
        refine htr0 ?_
        have hbL : algebraMap K L β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hb0
        have hτ : τ = algebraMap K L (-(g / β₀)) := by
          rw [map_neg, map_div₀]
          field_simp
          linear_combination hb'
        rw [hτ]
        exact isAlgebraic_algebraMap _
    have hcast := congrArg (fun z : ↥E => (z : L)) hueq
    simp only [hφ] at hcast
    push_cast [hcoez] at hcast
    simp only [haE, hcE] at hcast
    have hc1 : aK ^ (-j) * c ≠ 0 := mul_ne_zero (zpow_ne_zero _ haK0) hc
    have e1 : algebraMap K L (aK ^ (-j) * c)
        = (algebraMap K L aK) ^ (-j) * algebraMap K L c := by rw [map_mul, map_zpow₀]
    have hrel1 : Fr.σ (u : L) = algebraMap K L (aK ^ (-j) * c) * (u : L)
        + (algebraMap K L 0 * τ + algebraMap K L 0) := by
      rw [e1, map_zero, zero_mul, add_zero, add_zero]
      linear_combination hcast
    rcases level_one_classification Fr hq hshift htr0 huL u.2 hc1 hrel1 with
        ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', hw'0, hh'0, hh'src, hw'eq⟩ |
        ⟨u', j', hu'0, -, -, huval, hueq'⟩
    · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
    · exact absurd (by rcases hh'src with hh | hh <;> rw [hh] <;> simp) hh'0
    · have haKzpow : aK ^ (-j) = q ^ (-j) * Fr.ρ ^ j := by
        have hd : aK ^ (-j) = q ^ (-j) / Fr.ρ ^ (-j) := by rw [haKdef, div_zpow]
        rw [hd, zpow_neg Fr.ρ j, div_eq_mul_inv, inv_inv]
      have hpair : q ^ (-j') * (aK ^ (-j) * c) = q ^ (i - j - j') * Fr.ρ ^ (k + j) := by
        rw [haKzpow, hcik, zpow_add₀ hρ0,
          show i - j - j' = i + (-j) + (-j') by ring, zpow_add₀ hq, zpow_add₀ hq]
        ring
      by_cases htriv : i - j - j' = 0 ∧ k + j = 0
      · refine Or.inr (Or.inr ⟨u', j', j, hu'0, ?_, hαzero, hβzero.1, hβzero.2, ?_, by omega,
          by omega⟩)
        · rw [hueq', hpair, htriv.1, htriv.2, zpow_zero, zpow_zero, one_mul, one_mul]
        · rw [hVeq]
          have huval' : algebraMap ↥E L u = (u : L) := rfl
          rw [huval', huval]
      · exact Or.inl ⟨u', i - j - j', k + j, hu'0, htriv, by rw [hueq', hpair]⟩

end GaloisForLFunctions.HTGeometry
