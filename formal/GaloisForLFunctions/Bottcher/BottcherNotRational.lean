/-
# The Böttcher coordinate is not rational — invariant-set brick

Toward the `u₀`-degree-0 residue of the `u₀ ⟂ φ` cards at `φ`-degree 1: no rational function
agrees with `bottcherCoord c` on the escape far field, `c ≠ 0`.

This file proves the geometric core, entirely elementarily:

* `quadratic_mem_escapeOpen` — the escape far field is forward invariant;
* `escapeOpen_infinite` — it is infinite (large real ray);
* **`invariant_finite_empty`** — a FINITE set `T ⊆ ℂ` with the two-sided invariance
  `a ∈ T ↔ z²+c ∈ T` is empty when `c ≠ 0`.  The square-root selector `σ : T → T` (a root of
  `w² = b − c`; it lies in `T` by the backward direction) satisfies `f ∘ σ = id`, so it is
  injective; `-σ` is a second injection; the two images meet at most in `{0}`.
  Inclusion–exclusion forces `#T ≤ 1`, then `T = {b₀}` gives `σ b₀ = b₀ = -σ b₀`, so `b₀ = 0`
  and `c = f(0) ∈ T = {0}` — contradiction.

Next increment (see the u0 worklog plan): a coprime rational representation `q·φ = p` on
`escapeOpen c` plus the functional equation `bottcherCoord_quadratic` yields (on an infinite set,
hence as polynomials) `q∘f·p² = p∘f·q²`; coprimality composes (Bézout), so `q∘f = α q²`,
`p∘f = β p²`, making the root sets of `p, q` two-sidedly invariant, hence empty by this brick;
`p, q` are then constants, so `φ` is a constant `κ` with `κ = κ²`, `κ ≠ 0` (exponential), i.e.
`κ = 1` — contradicting `one_lt_norm_bottcherCoord`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex Polynomial Bottcher

namespace BottcherNotRational

/-- Forward invariance of the escape far field. -/
theorem quadratic_mem_escapeOpen {c w : ℂ} (hw : w ∈ escapeOpen c) :
    quadratic c w ∈ escapeOpen c := by
  obtain ⟨hcw, h2w⟩ := mem_escapeOpen_regime hw
  have hmax : max 2 ‖c‖ < ‖w‖ := hw
  show max 2 ‖c‖ < ‖w ^ 2 + c‖
  have htri : ‖w ^ 2‖ ≤ ‖w ^ 2 + c‖ + ‖(-c : ℂ)‖ := by
    calc ‖w ^ 2‖ = ‖w ^ 2 + c + (-c)‖ := by ring_nf
      _ ≤ ‖w ^ 2 + c‖ + ‖(-c : ℂ)‖ := norm_add_le _ _
  rw [norm_neg] at htri
  have hp : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
  have h3 : ‖c‖ ≤ max 2 ‖c‖ := le_max_right _ _
  nlinarith [htri, hp, hmax, h3, h2w, mul_pos (sub_pos.mpr h2w)
    (sub_pos.mpr (lt_of_le_of_lt h3 hmax))]

/-- The escape far field is infinite (it contains the large real ray). -/
theorem escapeOpen_infinite (c : ℂ) : (escapeOpen c).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((max 2 ‖c‖ + 1 + n : ℝ) : ℂ))
  · intro m n hmn
    have h := congrArg Complex.re hmn
    simp only [Complex.ofReal_re] at h
    have hmn' : (m : ℝ) = n := by linarith [h]
    exact_mod_cast hmn'
  · intro n
    show max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 + n : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- **A finite set with two-sided quadratic invariance is empty** (`c ≠ 0`). -/
theorem invariant_finite_empty {c : ℂ} (hc : c ≠ 0) {T : Set ℂ} (hfin : T.Finite)
    (hinv : ∀ a : ℂ, a ∈ T ↔ quadratic c a ∈ T) : T = ∅ := by
  classical
  by_contra hne
  have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  -- the square-root selector
  have hsel : ∀ b ∈ T, ∃ z : ℂ, z ^ 2 = b - c := fun b _ =>
    IsAlgClosed.exists_pow_nat_eq (b - c) (by norm_num)
  choose σ hσ using hsel
  have hfσ : ∀ b (hb : b ∈ T), quadratic c (σ b hb) = b := by
    intro b hb
    show σ b hb ^ 2 + c = b
    rw [hσ b hb]; ring
  have hfnσ : ∀ b (hb : b ∈ T), quadratic c (-σ b hb) = b := by
    intro b hb
    show (-σ b hb) ^ 2 + c = b
    rw [neg_sq, hσ b hb]; ring
  have hσT : ∀ b (hb : b ∈ T), σ b hb ∈ T := by
    intro b hb
    rw [hinv, hfσ b hb]; exact hb
  have hnσT : ∀ b (hb : b ∈ T), -σ b hb ∈ T := by
    intro b hb
    rw [hinv, hfnσ b hb]; exact hb
  -- the two image sets
  set S₁ : Set ℂ := {z | ∃ b, ∃ hb : b ∈ T, z = σ b hb} with hS₁
  set S₂ : Set ℂ := {z | ∃ b, ∃ hb : b ∈ T, z = -σ b hb} with hS₂
  have hS₁T : S₁ ⊆ T := by rintro z ⟨b, hb, rfl⟩; exact hσT b hb
  have hS₂T : S₂ ⊆ T := by rintro z ⟨b, hb, rfl⟩; exact hnσT b hb
  have hfin₁ : S₁.Finite := hfin.subset hS₁T
  have hfin₂ : S₂.Finite := hfin.subset hS₂T
  -- the images meet at most in 0
  have hmeet : S₁ ∩ S₂ ⊆ ({0} : Set ℂ) := by
    rintro z ⟨⟨b, hb, rfl⟩, ⟨b', hb', hz'⟩⟩
    have h2 : quadratic c (σ b hb) = b' := by
      have hq : quadratic c (σ b hb) = quadratic c (-σ b' hb') := by rw [← hz']
      rw [hq, hfnσ b' hb']
    have hbb' : b = b' := by rw [← hfσ b hb, h2]
    subst hbb'
    have hzz : σ b hb = -σ b hb := hz'
    have h20 : (2 : ℂ) * σ b hb = 0 := by linear_combination hzz
    rcases mul_eq_zero.mp h20 with h | h
    · exact absurd h two_ne_zero
    · simpa using h
  -- T is the quadratic image of S₁, so #T ≤ #S₁; and S₁ ⊆ T gives equality
  have hTimg : T = (quadratic c) '' S₁ := by
    apply Set.eq_of_subset_of_subset
    · intro b hb
      exact ⟨σ b hb, ⟨b, hb, rfl⟩, hfσ b hb⟩
    · rintro x ⟨z, ⟨b, hb, rfl⟩, rfl⟩
      rw [hfσ b hb]; exact hb
  have hcard₁ : T.ncard ≤ S₁.ncard := by
    rw [hTimg]; exact Set.ncard_image_le hfin₁
  have hS₁card : S₁.ncard = T.ncard :=
    le_antisymm (Set.ncard_le_ncard hS₁T hfin) hcard₁
  have hS₂img : S₂ = (fun z => -z) '' S₁ := by
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨σ b hb, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨b, hb, rfl⟩, rfl⟩; exact ⟨b, hb, rfl⟩
  have hS₂card : S₂.ncard = T.ncard := by
    rw [hS₂img, Set.ncard_image_of_injective _ neg_injective, hS₁card]
  -- inclusion–exclusion forces #T ≤ 1
  have hinter : (S₁ ∩ S₂).ncard ≤ 1 := by
    calc (S₁ ∩ S₂).ncard ≤ ({0} : Set ℂ).ncard :=
      Set.ncard_le_ncard hmeet (Set.finite_singleton 0)
      _ = 1 := Set.ncard_singleton 0
  have hie : (S₁ ∪ S₂).ncard + (S₁ ∩ S₂).ncard = S₁.ncard + S₂.ncard :=
    Set.ncard_union_add_ncard_inter S₁ S₂ hfin₁ hfin₂
  have hunion : (S₁ ∪ S₂).ncard ≤ T.ncard :=
    Set.ncard_le_ncard (Set.union_subset hS₁T hS₂T) hfin
  have hTpos : 0 < T.ncard := (Set.ncard_pos hfin).mpr hTne
  have hTone : T.ncard = 1 := by omega
  -- a singleton is impossible
  obtain ⟨b₀, hb₀T⟩ := Set.ncard_eq_one.mp hTone
  have hb₀ : b₀ ∈ T := by rw [hb₀T]; rfl
  have h1 : σ b₀ hb₀ = b₀ := by
    have := hσT b₀ hb₀; rw [hb₀T] at this; exact this
  have h2 : -σ b₀ hb₀ = b₀ := by
    have := hnσT b₀ hb₀; rw [hb₀T] at this; exact this
  have hb₀0 : b₀ = 0 := by
    have h20 : (2 : ℂ) * b₀ = 0 := by linear_combination -h1 - h2
    rcases mul_eq_zero.mp h20 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hcT : quadratic c b₀ ∈ T := (hinv b₀).mp hb₀
  rw [hb₀0] at hcT
  have hcT' : c ∈ T := by
    have : quadratic c 0 = c := by
      show (0 : ℂ) ^ 2 + c = c
      ring
    rwa [this] at hcT
  rw [hb₀T, hb₀0] at hcT'
  exact hc (by simpa using hcT')

end BottcherNotRational

namespace BottcherNotRational

/-- Multiplicity of a power of a linear factor. -/
theorem rootMultiplicity_linear_pow (a r : ℂ) (m : ℕ) :
    rootMultiplicity a ((X - C r) ^ m) = m * (if a = r then 1 else 0) := by
  induction m with
  | zero =>
    rw [pow_zero]
    rw [rootMultiplicity_eq_zero (by simp [IsRoot])]
    ring
  | succ n ih =>
    have hne : (X - C r) ^ n * (X - C r) ≠ 0 :=
      (((monic_X_sub_C r).pow n).mul (monic_X_sub_C r)).ne_zero
    rw [pow_succ, rootMultiplicity_mul hne, ih]
    split_ifs with h
    · subst h
      rw [rootMultiplicity_X_sub_C_self]
      ring
    · rw [rootMultiplicity_eq_zero (by simp [IsRoot, sub_eq_zero, h])]
      ring

/-- **Quadratic-composition multiplicity**: `μ_a(q∘(X²+c)) = e_a · μ_{a²+c}(q)` with `e_a = 2`
at `a = 0` and `e_a = 1` otherwise. -/
theorem rootMultiplicity_comp_quadratic {q : Polynomial ℂ} (hq : q ≠ 0) (c a : ℂ) :
    rootMultiplicity a (q.comp (X ^ 2 + C c))
      = (if a = 0 then 2 else 1) * rootMultiplicity (a ^ 2 + c) q := by
  set b : ℂ := a ^ 2 + c with hb
  set m : ℕ := rootMultiplicity b q with hm
  set u : Polynomial ℂ := q /ₘ (X - C b) ^ m with hu
  have hdecomp : (X - C b) ^ m * u = q := pow_mul_divByMonic_rootMultiplicity_eq q b
  have hune : u.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hq
  have hcomp : q.comp (X ^ 2 + C c)
      = ((X - C b) ^ m).comp (X ^ 2 + C c) * u.comp (X ^ 2 + C c) := by
    rw [← hdecomp, mul_comp]
  have hlin : (X - C b).comp (X ^ 2 + C c) = (X - C a) * (X + C a) := by
    rw [sub_comp, X_comp, C_comp, hb, map_add, map_pow]
    ring
  have hpowlin : ((X - C b) ^ m).comp (X ^ 2 + C c) = ((X - C a) * (X + C a)) ^ m := by
    rw [pow_comp, hlin]
  have hueval : (u.comp (X ^ 2 + C c)).eval a ≠ 0 := by
    rw [eval_comp]
    have : (X ^ 2 + C c).eval a = b := by rw [hb]; simp
    rwa [this]
  have hu0 : rootMultiplicity a (u.comp (X ^ 2 + C c)) = 0 :=
    rootMultiplicity_eq_zero (fun h => hueval h)
  have hpowne : ((X - C a) * (X + C a)) ^ m ≠ 0 := by
    have h1 : Monic ((X - C a) * (X + C a)) := by
      have : X + C a = X - C (-a) := by rw [map_neg, sub_neg_eq_add]
      rw [this]
      exact (monic_X_sub_C a).mul (monic_X_sub_C (-a))
    exact (h1.pow m).ne_zero
  have hucompne : u.comp (X ^ 2 + C c) ≠ 0 := fun h => hueval (by rw [h]; simp)
  have hprodne : ((X - C a) * (X + C a)) ^ m * u.comp (X ^ 2 + C c) ≠ 0 :=
    mul_ne_zero hpowne hucompne
  rw [hcomp, hpowlin, rootMultiplicity_mul hprodne, hu0, add_zero]
  have hsplit : ((X - C a) * (X + C a)) ^ m = (X - C a) ^ m * (X - C (-a)) ^ m := by
    rw [← mul_pow]
    congr 1
    rw [map_neg, sub_neg_eq_add]
  have hsplitne : (X - C a) ^ m * (X - C (-a)) ^ m ≠ 0 :=
    mul_ne_zero ((monic_X_sub_C a).pow m).ne_zero ((monic_X_sub_C (-a)).pow m).ne_zero
  rw [hsplit, rootMultiplicity_mul hsplitne, rootMultiplicity_linear_pow,
    rootMultiplicity_linear_pow, if_pos rfl]
  by_cases h0 : a = 0
  · rw [if_pos h0, if_pos (by rw [h0]; ring)]
    ring
  · rw [if_neg h0, if_neg (fun h => h0 (by
      have h2 : (2 : ℂ) * a = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h))]
    ring

end BottcherNotRational
