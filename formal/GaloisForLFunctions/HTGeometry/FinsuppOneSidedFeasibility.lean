import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.NNReal.Defs

/-!
# One-sided linear feasibility over finitely supported sequences

Let `T : ι → (J →₀ ℝ)` be a family of finitely supported vectors, `D : ι → ℝ` and `U : J → ℝ`.
Assume every coordinate direction is reachable negatively: for every `j`, some `T i` is a negative
multiple of `e_j`.

**Theorem** (`exists_le_of_nonneg_on_nonpos_cone`). If every nonnegative combination `c` with
`Σ c_i T_i ≤ 0` satisfies `⟨U, Σ c_i T_i⟩ ≤ Σ c_i D_i`, then there is `lam : J → ℝ` with
`lam ≤ U` and `⟨lam, T_i⟩ ≤ D_i` for every `i`.

**Proof.** Apply the M. Riesz extension theorem to the functional `(0, t) ↦ t` and the cone
generated in `(J →₀ ℝ) × ℝ` by `(T_i, D_i)`, `(e_j, U_j)` and `(0, 1)`. Every element of the cone
carries a certificate `c ≥ 0` with `Σ c_i T_i ≤ x₁` and `Σ c_i D_i + ⟨U, x₁ − Σ c_i T_i⟩ ≤ x₂`. So
the functional is nonnegative on the cone exactly by the hypothesis. The extension `g` gives
`lam_j = −g(e_j, 0)`.
-/

open Finsupp
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

variable {ι J : Type*}

/-- **One-sided feasibility.** Nonnegativity on the cone of nonpositive combinations gives a
dominated solution of the linear constraints. -/
theorem exists_le_of_nonneg_on_nonpos_cone (T : ι → (J →₀ ℝ)) (D : ι → ℝ) (U : J → ℝ)
    (hT : ∀ j, ∃ i, ∃ a : ℝ, 0 < a ∧ T i = Finsupp.single j (-a))
    (hyp : ∀ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) → (∀ j, linearCombination ℝ T c j ≤ 0) →
      linearCombination ℝ U (linearCombination ℝ T c) ≤ linearCombination ℝ D c) :
    ∃ lam : J → ℝ, (∀ j, lam j ≤ U j) ∧ ∀ i, linearCombination ℝ lam (T i) ≤ D i := by
  classical
  let G : Set ((J →₀ ℝ) × ℝ) := Set.range (fun i => (T i, D i)) ∪
    Set.range (fun j => (Finsupp.single j (1 : ℝ), U j)) ∪ {((0 : J →₀ ℝ), (1 : ℝ))}
  let s : PointedCone ℝ ((J →₀ ℝ) × ℝ) := PointedCone.hull ℝ G
  have hTs : ∀ i, (T i, D i) ∈ s := fun i =>
    PointedCone.subset_hull (Or.inl (Or.inl ⟨i, rfl⟩))
  have hUs : ∀ j, (Finsupp.single j (1 : ℝ), U j) ∈ s := fun j =>
    PointedCone.subset_hull (Or.inl (Or.inr ⟨j, rfl⟩))
  -- every element of the cone carries a certificate
  have hQ : ∀ x ∈ s, ∃ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) ∧
      (∀ j, linearCombination ℝ T c j ≤ x.1 j) ∧
      linearCombination ℝ D c + linearCombination ℝ U (x.1 - linearCombination ℝ T c) ≤ x.2 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (⟨i, rfl⟩ | ⟨j, rfl⟩) | hx
      · refine ⟨Finsupp.single i 1, fun i' => ?_, fun j => ?_, ?_⟩
        · by_cases h : i = i' <;> simp [h]
        · simp
        · simp
      · refine ⟨0, fun _ => le_rfl, fun j' => ?_, ?_⟩
        · by_cases h : j = j' <;> simp [h]
        · simp
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨0, fun _ => le_rfl, fun _ => by simp, by simp⟩
    | zero => exact ⟨0, fun _ => le_rfl, fun _ => by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, h₁, h₁', h₁''⟩ := hx
      obtain ⟨c₂, h₂, h₂', h₂''⟩ := hy
      refine ⟨c₁ + c₂, fun i => add_nonneg (h₁ i) (h₂ i), fun j => ?_, ?_⟩
      · rw [map_add, Finsupp.coe_add, Pi.add_apply, Prod.fst_add, Finsupp.coe_add, Pi.add_apply]
        linarith [h₁' j, h₂' j]
      · have e : (x + y).1 - linearCombination ℝ T (c₁ + c₂) =
            (x.1 - linearCombination ℝ T c₁) + (y.1 - linearCombination ℝ T c₂) := by
          rw [map_add, Prod.fst_add]; abel
        rw [e, map_add, map_add, Prod.snd_add]
        linarith
    | smul t x _ hx =>
      obtain ⟨c, h, h', h''⟩ := hx
      have ht : (0 : ℝ) ≤ t := t.2
      rw [show t • x = (t : ℝ) • x from rfl]
      refine ⟨(t : ℝ) • c, fun i => mul_nonneg ht (h i), fun j => ?_, ?_⟩
      · rw [map_smul, Prod.smul_fst, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
          smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h' j) ht
      · rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_smul, map_smul, ← smul_sub, map_smul,
          smul_eq_mul, smul_eq_mul, ← mul_add]
        exact mul_le_mul_of_nonneg_left h'' ht
  -- every first coordinate is reachable
  have hreach : ∀ v : J →₀ ℝ, ∃ r : ℝ, (v, r) ∈ s := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨0, s.zero_mem⟩
    | add f g hf hg =>
      obtain ⟨r₁, h₁⟩ := hf
      obtain ⟨r₂, h₂⟩ := hg
      exact ⟨r₁ + r₂, s.add_mem h₁ h₂⟩
    | single j b =>
      rcases le_or_gt 0 b with hb | hb
      · refine ⟨b * U j, ?_⟩
        have := PointedCone.smul_mem s hb (hUs j)
        convert this using 1
        rw [Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
      · obtain ⟨i, a, ha, hTi⟩ := hT j
        refine ⟨(-b / a) * D i, ?_⟩
        have hc : (0 : ℝ) ≤ -b / a := div_nonneg (by linarith) ha.le
        have := PointedCone.smul_mem s hc (hTs i)
        convert this using 1
        rw [Prod.smul_mk, hTi, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
        congr 2
        field_simp
  -- the functional `(0, t) ↦ t`
  let p : Submodule ℝ ((J →₀ ℝ) × ℝ) := Submodule.prod ⊥ ⊤
  let f : (J →₀ ℝ) × ℝ →ₗ.[ℝ] ℝ := ⟨p, (LinearMap.snd ℝ (J →₀ ℝ) ℝ).comp p.subtype⟩
  have hf : ∀ x : f.domain, f x = (x : (J →₀ ℝ) × ℝ).2 := fun _ => rfl
  have hp : ∀ x : f.domain, (x : (J →₀ ℝ) × ℝ).1 = 0 := fun x =>
    (Submodule.mem_bot ℝ).mp (Submodule.mem_prod.mp x.2).1
  obtain ⟨g, hgf, hgs⟩ := riesz_extension s f (fun x hx => by
      obtain ⟨c, hc, hc', hc''⟩ := hQ _ hx
      rw [hf]
      rw [hp x] at hc' hc''
      have h1 := hyp c hc fun j => by simpa using hc' j
      rw [zero_sub, map_neg] at hc''
      linarith)
    (fun y => by
      obtain ⟨r, hr⟩ := hreach y.1
      refine ⟨⟨((0 : J →₀ ℝ), r - y.2), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, trivial⟩⟩, ?_⟩
      convert hr using 1
      ext <;> simp)
  have hg0 : ∀ t : ℝ, g ((0 : J →₀ ℝ), t) = t := fun t =>
    hgf ⟨((0 : J →₀ ℝ), t), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, trivial⟩⟩
  refine ⟨fun j => -g (Finsupp.single j 1, 0), fun j => ?_, fun i => ?_⟩
  · have h1 := hgs _ (hUs j)
    have e : (Finsupp.single j (1 : ℝ), U j) = (Finsupp.single j 1, 0) + ((0 : J →₀ ℝ), U j) := by
      ext <;> simp
    rw [e, map_add, hg0] at h1
    linarith
  · have hlin : (g.comp (LinearMap.inl ℝ (J →₀ ℝ) ℝ)) =
        -linearCombination ℝ (fun j => -g (Finsupp.single j 1, 0)) := by
      refine Finsupp.lhom_ext fun j b => ?_
      have e : ((Finsupp.single j b : J →₀ ℝ), (0 : ℝ)) = b • (Finsupp.single j 1, 0) := by
        ext <;> simp
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.neg_apply,
        linearCombination_single, smul_eq_mul, e, map_smul]
      ring
    have h1 := hgs _ (hTs i)
    have e : (T i, D i) = (T i, 0) + ((0 : J →₀ ℝ), D i) := by ext <;> simp
    rw [e, map_add, hg0] at h1
    have h2 := congrArg (fun φ => φ (T i)) hlin
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.neg_apply] at h2
    linarith

theorem linearCombination_neg {M : Type*} [AddCommGroup M] [Module ℝ M] (T : ι → M)
    (c : ι →₀ ℝ) : linearCombination ℝ (fun i => -T i) c = -linearCombination ℝ T c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, neg_add]
  | single i b => simp

/-- **One-sided feasibility, lower form.** Nonnegativity on the cone of nonnegative combinations
gives a solution bounded below by `L`. -/
theorem exists_ge_of_nonneg_on_nonneg_cone (T : ι → (J →₀ ℝ)) (D : ι → ℝ) (L : J → ℝ)
    (hT : ∀ j, ∃ i, ∃ a : ℝ, 0 < a ∧ T i = Finsupp.single j a)
    (hyp : ∀ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ linearCombination ℝ T c j) →
      linearCombination ℝ L (linearCombination ℝ T c) ≤ linearCombination ℝ D c) :
    ∃ lam : J → ℝ, (∀ j, L j ≤ lam j) ∧ ∀ i, linearCombination ℝ lam (T i) ≤ D i := by
  obtain ⟨μ, hμ, hμT⟩ := exists_le_of_nonneg_on_nonpos_cone (fun i => -T i) D (fun j => -L j)
    (fun j => by
      obtain ⟨i, a, ha, h⟩ := hT j
      exact ⟨i, a, ha, by rw [h, Finsupp.single_neg]⟩)
    (fun c hc hcT => by
      rw [linearCombination_neg] at hcT ⊢
      have h1 := hyp c hc fun j => by simpa using hcT j
      rw [linearCombination_neg, map_neg, neg_neg]
      exact h1)
  refine ⟨fun j => -μ j, fun j => by linarith [hμ j], fun i => ?_⟩
  rw [linearCombination_neg]
  have := hμT i
  rw [map_neg] at this
  exact this

/-- **Two-sided feasibility.** If every coordinate direction is reachable with both signs and
every nonnegative combination `c` with `Σ c_i T_i = 0` has `Σ c_i D_i ≥ 0`, then some
`lam : J → ℝ` has `⟨lam, T_i⟩ ≤ D_i` for every `i`. -/
theorem exists_of_nonneg_on_null_cone (T : ι → (J →₀ ℝ)) (D : ι → ℝ)
    (hTneg : ∀ j, ∃ i, ∃ a : ℝ, 0 < a ∧ T i = Finsupp.single j (-a))
    (hTpos : ∀ j, ∃ i, ∃ a : ℝ, 0 < a ∧ T i = Finsupp.single j a)
    (hyp : ∀ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) → linearCombination ℝ T c = 0 →
      0 ≤ linearCombination ℝ D c) :
    ∃ lam : J → ℝ, ∀ i, linearCombination ℝ lam (T i) ≤ D i := by
  classical
  let G : Set ((J →₀ ℝ) × ℝ) := Set.range (fun i => (T i, D i)) ∪ {((0 : J →₀ ℝ), (1 : ℝ))}
  let s : PointedCone ℝ ((J →₀ ℝ) × ℝ) := PointedCone.hull ℝ G
  have hTs : ∀ i, (T i, D i) ∈ s := fun i => PointedCone.subset_hull (Or.inl ⟨i, rfl⟩)
  have hQ : ∀ x ∈ s, ∃ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) ∧ linearCombination ℝ T c = x.1 ∧
      linearCombination ℝ D c ≤ x.2 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | hx
      · refine ⟨Finsupp.single i 1, fun i' => ?_, by simp, by simp⟩
        by_cases h : i = i' <;> simp [h]
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨0, fun _ => le_rfl, by simp, by simp⟩
    | zero => exact ⟨0, fun _ => le_rfl, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, h₁, h₁', h₁''⟩ := hx
      obtain ⟨c₂, h₂, h₂', h₂''⟩ := hy
      refine ⟨c₁ + c₂, fun i => add_nonneg (h₁ i) (h₂ i), ?_, ?_⟩
      · rw [map_add, h₁', h₂', Prod.fst_add]
      · rw [map_add, Prod.snd_add]; linarith
    | smul t x _ hx =>
      obtain ⟨c, h, h', h''⟩ := hx
      have ht : (0 : ℝ) ≤ t := t.2
      rw [show t • x = (t : ℝ) • x from rfl]
      refine ⟨(t : ℝ) • c, fun i => mul_nonneg ht (h i), ?_, ?_⟩
      · rw [map_smul, h', Prod.smul_fst]
      · rw [map_smul, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left h'' ht
  have hreach : ∀ v : J →₀ ℝ, ∃ r : ℝ, (v, r) ∈ s := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨0, s.zero_mem⟩
    | add f g hf hg =>
      obtain ⟨r₁, h₁⟩ := hf
      obtain ⟨r₂, h₂⟩ := hg
      exact ⟨r₁ + r₂, s.add_mem h₁ h₂⟩
    | single j b =>
      rcases le_or_gt 0 b with hb | hb
      · obtain ⟨i, a, ha, hTi⟩ := hTpos j
        refine ⟨(b / a) * D i, ?_⟩
        have hc : (0 : ℝ) ≤ b / a := div_nonneg hb ha.le
        have := PointedCone.smul_mem s hc (hTs i)
        convert this using 1
        rw [Prod.smul_mk, hTi, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
        congr 2
        field_simp
      · obtain ⟨i, a, ha, hTi⟩ := hTneg j
        refine ⟨(-b / a) * D i, ?_⟩
        have hc : (0 : ℝ) ≤ -b / a := div_nonneg (by linarith) ha.le
        have := PointedCone.smul_mem s hc (hTs i)
        convert this using 1
        rw [Prod.smul_mk, hTi, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
        congr 2
        field_simp
  let p : Submodule ℝ ((J →₀ ℝ) × ℝ) := Submodule.prod ⊥ ⊤
  let f : (J →₀ ℝ) × ℝ →ₗ.[ℝ] ℝ := ⟨p, (LinearMap.snd ℝ (J →₀ ℝ) ℝ).comp p.subtype⟩
  have hf : ∀ x : f.domain, f x = (x : (J →₀ ℝ) × ℝ).2 := fun _ => rfl
  have hp : ∀ x : f.domain, (x : (J →₀ ℝ) × ℝ).1 = 0 := fun x =>
    (Submodule.mem_bot ℝ).mp (Submodule.mem_prod.mp x.2).1
  obtain ⟨g, hgf, hgs⟩ := riesz_extension s f (fun x hx => by
      obtain ⟨c, hc, hc', hc''⟩ := hQ _ hx
      rw [hf]
      rw [hp x] at hc'
      linarith [hyp c hc hc'])
    (fun y => by
      obtain ⟨r, hr⟩ := hreach y.1
      refine ⟨⟨((0 : J →₀ ℝ), r - y.2), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, trivial⟩⟩, ?_⟩
      convert hr using 1
      ext <;> simp)
  have hg0 : ∀ t : ℝ, g ((0 : J →₀ ℝ), t) = t := fun t =>
    hgf ⟨((0 : J →₀ ℝ), t), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, trivial⟩⟩
  refine ⟨fun j => -g (Finsupp.single j 1, 0), fun i => ?_⟩
  have hlin : (g.comp (LinearMap.inl ℝ (J →₀ ℝ) ℝ)) =
      -linearCombination ℝ (fun j => -g (Finsupp.single j 1, 0)) := by
    refine Finsupp.lhom_ext fun j b => ?_
    have e : ((Finsupp.single j b : J →₀ ℝ), (0 : ℝ)) = b • (Finsupp.single j 1, 0) := by
      ext <;> simp
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.neg_apply,
      linearCombination_single, smul_eq_mul, e, map_smul]
    ring
  have h1 := hgs _ (hTs i)
  have e : (T i, D i) = (T i, 0) + ((0 : J →₀ ℝ), D i) := by ext <;> simp
  rw [e, map_add, hg0] at h1
  have h2 := congrArg (fun φ => φ (T i)) hlin
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.neg_apply] at h2
  linarith

end GaloisForLFunctions.HTGeometry
