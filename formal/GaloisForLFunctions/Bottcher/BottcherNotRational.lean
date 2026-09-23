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
  show max 2 ‖c‖ < ‖w ^ (2 : ℕ) + c‖
  have htri : ‖w ^ (2 : ℕ)‖ ≤ ‖w ^ (2 : ℕ) + c‖ + ‖(-c : ℂ)‖ := by
    calc ‖w ^ (2 : ℕ)‖ = ‖w ^ (2 : ℕ) + c + (-c)‖ := by ring_nf
      _ ≤ ‖w ^ (2 : ℕ) + c‖ + ‖(-c : ℂ)‖ := norm_add_le _ _
  rw [norm_neg] at htri
  have hp : ‖w ^ (2 : ℕ)‖ = ‖w‖ ^ (2 : ℕ) := norm_pow w 2
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
  have hsel : ∀ b ∈ T, ∃ z : ℂ, z ^ (2 : ℕ) = b - c := fun b _ =>
    IsAlgClosed.exists_pow_nat_eq (b - c) (by norm_num)
  choose σ hσ using hsel
  have hfσ : ∀ b (hb : b ∈ T), quadratic c (σ b hb) = b := by
    intro b hb
    show σ b hb ^ (2 : ℕ) + c = b
    rw [hσ b hb]; ring
  have hfnσ : ∀ b (hb : b ∈ T), quadratic c (-σ b hb) = b := by
    intro b hb
    show (-σ b hb) ^ (2 : ℕ) + c = b
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
      show (0 : ℂ) ^ (2 : ℕ) + c = c
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
    rootMultiplicity a (q.comp (X ^ (2 : ℕ) + C c))
      = (if a = 0 then 2 else 1) * rootMultiplicity (a ^ (2 : ℕ) + c) q := by
  set b : ℂ := a ^ (2 : ℕ) + c with hb
  set m : ℕ := rootMultiplicity b q with hm
  set u : Polynomial ℂ := q /ₘ (X - C b) ^ m with hu
  have hdecomp : (X - C b) ^ m * u = q := pow_mul_divByMonic_rootMultiplicity_eq q b
  have hune : u.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hq
  have hcomp : q.comp (X ^ (2 : ℕ) + C c)
      = ((X - C b) ^ m).comp (X ^ (2 : ℕ) + C c) * u.comp (X ^ (2 : ℕ) + C c) := by
    rw [← hdecomp, mul_comp]
  have hlin : (X - C b).comp (X ^ (2 : ℕ) + C c) = (X - C a) * (X + C a) := by
    rw [sub_comp, X_comp, C_comp, hb, map_add, map_pow]
    ring
  have hpowlin : ((X - C b) ^ m).comp (X ^ (2 : ℕ) + C c) = ((X - C a) * (X + C a)) ^ m := by
    rw [pow_comp, hlin]
  have hueval : (u.comp (X ^ (2 : ℕ) + C c)).eval a ≠ 0 := by
    rw [eval_comp]
    have : (X ^ (2 : ℕ) + C c).eval a = b := by rw [hb]; simp
    rwa [this]
  have hu0 : rootMultiplicity a (u.comp (X ^ (2 : ℕ) + C c)) = 0 :=
    rootMultiplicity_eq_zero (fun h => hueval h)
  have hpowne : ((X - C a) * (X + C a)) ^ m ≠ 0 := by
    have h1 : Monic ((X - C a) * (X + C a)) := by
      have : X + C a = X - C (-a) := by rw [map_neg, sub_neg_eq_add]
      rw [this]
      exact (monic_X_sub_C a).mul (monic_X_sub_C (-a))
    exact (h1.pow m).ne_zero
  have hucompne : u.comp (X ^ (2 : ℕ) + C c) ≠ 0 := fun h => hueval (by rw [h]; simp)
  have hprodne : ((X - C a) * (X + C a)) ^ m * u.comp (X ^ (2 : ℕ) + C c) ≠ 0 :=
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

namespace BottcherNotRational

/-- The multiplicity defect `δ(a) = μ_a(p) − μ_a(q)` as an integer. -/
noncomputable def defect (p q : Polynomial ℂ) (a : ℂ) : ℤ :=
  (rootMultiplicity a p : ℤ) - (rootMultiplicity a q : ℤ)

/-- Chained defect doubling along a zero-free orbit segment. -/
theorem defect_iterate {p q : Polynomial ℂ} {c : ℂ}
    (hrel : ∀ a : ℂ, a ≠ 0 → defect p q (a ^ (2 : ℕ) + c) = 2 * defect p q a)
    (a : ℂ) (k : ℕ) (hfree : ∀ j < k, (quadratic c)^[j] a ≠ 0) :
    defect p q ((quadratic c)^[k] a) = 2 ^ k * defect p q a := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hfree' : ∀ j < n, (quadratic c)^[j] a ≠ 0 := fun j hj => hfree j (by omega)
    have hne : (quadratic c)^[n] a ≠ 0 := hfree n (by omega)
    rw [Function.iterate_succ_apply',
      show quadratic c ((quadratic c)^[n] a) = ((quadratic c)^[n] a) ^ (2 : ℕ) + c from rfl,
      hrel _ hne, ih hfree']
    ring

/-- **The Böttcher coordinate is not rational** (`c ≠ 0`): no polynomial identity
`q(w)·φ_c(w) = p(w)` with `q ≠ 0` can hold on the escape far field. -/
theorem bottcherCoord_not_rational {c : ℂ} (hc : c ≠ 0) (p q : Polynomial ℂ) (hq : q ≠ 0)
    (hrat : ∀ w ∈ escapeOpen c, q.eval w * bottcherCoord c w = p.eval w) : False := by
  classical
  -- p is nonzero
  have hp : p ≠ 0 := by
    intro hp0
    apply hq
    apply eq_zero_of_infinite_isRoot
    refine (escapeOpen_infinite c).mono ?_
    intro w hw
    have h1 := hrat w hw
    rw [hp0, eval_zero] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (bottcherCoord_ne_zero c w)
  -- the composed polynomials are nonzero
  set fpoly : Polynomial ℂ := X ^ (2 : ℕ) + C c with hfpoly
  have hfp_ne_const : fpoly ≠ C (fpoly.coeff 0) := by
    intro h
    have := congrArg (fun r => Polynomial.coeff r 2) h
    simp [hfpoly] at this
  have hqcomp : q.comp fpoly ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
    · exact hq h
    · exact hfp_ne_const h
  have hpcomp : p.comp fpoly ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
    · exact hp h
    · exact hfp_ne_const h
  have hfeval : ∀ w : ℂ, fpoly.eval w = w ^ (2 : ℕ) + c := by
    intro w; rw [hfpoly]; simp
  -- the key polynomial identity from the functional equation
  have hkey : q.comp fpoly * p ^ (2 : ℕ) = p.comp fpoly * q ^ (2 : ℕ) := by
    apply eq_of_infinite_eval_eq
    refine (escapeOpen_infinite c).mono ?_
    intro w hw
    obtain ⟨hcw, h2w⟩ := mem_escapeOpen_regime hw
    have hfw : quadratic c w ∈ escapeOpen c := quadratic_mem_escapeOpen hw
    have h1 := hrat w hw
    have h2 := hrat _ hfw
    have h3 := bottcherCoord_quadratic hcw h2w
    simp only [quadratic_apply] at h2 h3
    show (q.comp fpoly * p ^ (2 : ℕ)).eval w = (p.comp fpoly * q ^ (2 : ℕ)).eval w
    simp only [eval_mul, eval_pow, eval_comp, hfeval]
    linear_combination (-(q.eval (w ^ (2 : ℕ) + c)) * (q.eval w * bottcherCoord c w + p.eval w)) * h1
      + (q.eval w) ^ (2 : ℕ) * h2 + (-(q.eval (w ^ (2 : ℕ) + c)) * (q.eval w) ^ (2 : ℕ)) * h3
  -- the defect doubling relation
  have hrelδ : ∀ a : ℂ, a ≠ 0 → defect p q (a ^ (2 : ℕ) + c) = 2 * defect p q a := by
    intro a ha
    have hL : q.comp fpoly * p ^ (2 : ℕ) ≠ 0 := mul_ne_zero hqcomp (pow_ne_zero 2 hp)
    have hR : p.comp fpoly * q ^ (2 : ℕ) ≠ 0 := mul_ne_zero hpcomp (pow_ne_zero 2 hq)
    have hμ := congrArg (rootMultiplicity a) hkey
    rw [rootMultiplicity_mul hL, rootMultiplicity_mul hR] at hμ
    have hp2 : rootMultiplicity a (p ^ (2 : ℕ)) = 2 * rootMultiplicity a p := by
      rw [pow_two, rootMultiplicity_mul (mul_ne_zero hp hp)]; ring
    have hq2 : rootMultiplicity a (q ^ (2 : ℕ)) = 2 * rootMultiplicity a q := by
      rw [pow_two, rootMultiplicity_mul (mul_ne_zero hq hq)]; ring
    have hqc := rootMultiplicity_comp_quadratic hq c a
    have hpc := rootMultiplicity_comp_quadratic hp c a
    rw [if_neg ha, one_mul] at hqc hpc
    rw [hqc, hpc, hp2, hq2] at hμ
    unfold defect
    omega
  have hrelδ0 : defect p q c = defect p q 0 := by
    have hL : q.comp fpoly * p ^ (2 : ℕ) ≠ 0 := mul_ne_zero hqcomp (pow_ne_zero 2 hp)
    have hR : p.comp fpoly * q ^ (2 : ℕ) ≠ 0 := mul_ne_zero hpcomp (pow_ne_zero 2 hq)
    have hμ := congrArg (rootMultiplicity 0) hkey
    rw [rootMultiplicity_mul hL, rootMultiplicity_mul hR] at hμ
    have hp2 : rootMultiplicity 0 (p ^ (2 : ℕ)) = 2 * rootMultiplicity 0 p := by
      rw [pow_two, rootMultiplicity_mul (mul_ne_zero hp hp)]; ring
    have hq2 : rootMultiplicity 0 (q ^ (2 : ℕ)) = 2 * rootMultiplicity 0 q := by
      rw [pow_two, rootMultiplicity_mul (mul_ne_zero hq hq)]; ring
    have hqc := rootMultiplicity_comp_quadratic hq c 0
    have hpc := rootMultiplicity_comp_quadratic hp c 0
    rw [if_pos rfl] at hqc hpc
    have h0c : (0 : ℂ) ^ (2 : ℕ) + c = c := by ring
    rw [h0c] at hqc hpc
    rw [hqc, hpc, hp2, hq2] at hμ
    unfold defect
    omega
  -- the defect is bounded
  set B : ℕ := p.natDegree + q.natDegree with hB
  have hbound : ∀ a : ℂ, |defect p q a| ≤ (B : ℤ) := by
    intro a
    have h1 : rootMultiplicity a p ≤ p.natDegree := by
      rw [← count_roots]
      exact le_trans (Multiset.count_le_card a p.roots) (card_roots' p)
    have h2 : rootMultiplicity a q ≤ q.natDegree := by
      rw [← count_roots]
      exact le_trans (Multiset.count_le_card a q.roots) (card_roots' q)
    have hd : defect p q a = (rootMultiplicity a p : ℤ) - rootMultiplicity a q := rfl
    rw [hd, hB, abs_le]
    omega
  -- zero-free orbits kill the defect
  have horbit : ∀ a : ℂ, (∀ n : ℕ, (quadratic c)^[n] a ≠ 0) → defect p q a = 0 := by
    intro a hfree
    by_contra hδ
    have habs := abs_pos.mpr hδ
    have h1 : (1 : ℤ) ≤ |defect p q a| := by omega
    have h2 := defect_iterate hrelδ a (B + 1) (fun j _ => hfree j)
    have h3 : (2 : ℤ) ^ (B + 1) ≤ |defect p q ((quadratic c)^[B + 1] a)| := by
      rw [h2, abs_mul, abs_pow]
      calc (2 : ℤ) ^ (B + 1) = 2 ^ (B + 1) * 1 := by ring
        _ ≤ |(2 : ℤ)| ^ (B + 1) * |defect p q a| := by
            apply mul_le_mul
            · norm_num
            · exact h1
            · norm_num
            · positivity
    have h4 := hbound ((quadratic c)^[B + 1] a)
    have h5 : (B : ℤ) < 2 ^ (B + 1) := by
      calc (B : ℤ) < 2 ^ B := by exact_mod_cast Nat.lt_two_pow_self
        _ ≤ 2 ^ (B + 1) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    omega
  -- the defect vanishes at 0
  have hδ0 : defect p q 0 = 0 := by
    by_cases hper : ∃ n : ℕ, 1 ≤ n ∧ (quadratic c)^[n] 0 = 0
    · -- 0 is periodic: minimal period n ≥ 2, cycle relation kills δ(0)
      obtain ⟨n, hn1, hn0⟩ := hper
      have hex : ∃ m : ℕ, 1 ≤ m ∧ (quadratic c)^[m] 0 = 0 := ⟨n, hn1, hn0⟩
      set m := Nat.find hex with hm
      obtain ⟨hm1, hm0⟩ := Nat.find_spec hex
      have hm2 : 2 ≤ m := by
        by_contra h
        push Not at h
        have hm1' : m = 1 := by omega
        apply hc
        have h1 : (quadratic c)^[m] 0 = 0 := hm0
        rw [hm1'] at h1
        simpa [quadratic_apply] using h1
      -- along the cycle from c: no intermediate zeros
      have hcfree : ∀ j < m - 1, (quadratic c)^[j] c ≠ 0 := by
        intro j hj h0
        have hj1 : (quadratic c)^[j + 1] 0 = 0 := by
          rw [Function.iterate_succ_apply]
          have : quadratic c 0 = c := by simp [quadratic_apply]
          rw [this]
          exact h0
        have := Nat.find_min hex (m := j + 1) (by omega)
        push Not at this
        exact absurd hj1 (this (by omega))
      have hchain := defect_iterate hrelδ c (m - 1) hcfree
      have hcm : (quadratic c)^[m - 1] c = 0 := by
        have : (quadratic c)^[m - 1] c = (quadratic c)^[m] 0 := by
          rw [show m = (m - 1) + 1 from by omega, Function.iterate_succ_apply]
          congr 1
          simp [quadratic_apply]
        rw [this]
        exact hm0
      rw [hcm] at hchain
      -- δ(0) = 2^{m-1}·δ(c) = 2^{m-1}·δ(0), with 2^{m-1} ≥ 2
      rw [hrelδ0] at hchain
      have hpow : (2 : ℤ) ≤ 2 ^ (m - 1) := by
        calc (2 : ℤ) = 2 ^ (1 : ℕ) := by ring
          _ ≤ 2 ^ (m - 1) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
      have hfac : (2 ^ (m - 1) - 1 : ℤ) * defect p q 0 = 0 := by
        linear_combination -hchain
      have h1 : (2 ^ (m - 1) - 1 : ℤ) ≠ 0 := by omega
      exact (mul_eq_zero.mp hfac).resolve_left h1
    · -- 0 is not periodic: the orbit of c avoids 0, growth kills δ(c) = δ(0)
      push Not at hper
      have hcfree : ∀ n : ℕ, (quadratic c)^[n] c ≠ 0 := by
        intro n h0
        have : (quadratic c)^[n + 1] 0 = 0 := by
          rw [Function.iterate_succ_apply]
          have hq0 : quadratic c 0 = c := by simp [quadratic_apply]
          rw [hq0]
          exact h0
        exact absurd this (hper (n + 1) (by omega))
      rw [← hrelδ0]
      exact horbit c hcfree
  -- the defect vanishes everywhere
  have hδ : ∀ a : ℂ, defect p q a = 0 := by
    intro a
    by_cases hhit : ∃ k : ℕ, (quadratic c)^[k] a = 0
    · set k := Nat.find hhit with hk
      have hk0 : (quadratic c)^[k] a = 0 := Nat.find_spec hhit
      have hkfree : ∀ j < k, (quadratic c)^[j] a ≠ 0 := fun j hj => Nat.find_min hhit hj
      have hchain := defect_iterate hrelδ a k hkfree
      rw [hk0, hδ0] at hchain
      have h2k : (0 : ℤ) < 2 ^ k := by positivity
      nlinarith [hchain, h2k]
    · push Not at hhit
      exact horbit a hhit
  -- equal multiplicities: p and q are proportional
  have hroots : p.roots = q.roots := by
    ext a
    rw [count_roots, count_roots]
    have := hδ a
    unfold defect at this
    omega
  have hprop : p * C q.leadingCoeff = q * C p.leadingCoeff := by
    have hps := (IsAlgClosed.splits p).eq_prod_roots
    have hqs := (IsAlgClosed.splits q).eq_prod_roots
    rw [hroots] at hps
    generalize hlp : p.leadingCoeff = lp at hps ⊢
    generalize hlq : q.leadingCoeff = lq at hqs ⊢
    calc p * C lq = (C lp * (q.roots.map fun a => X - C a).prod) * C lq := by rw [← hps]
      _ = (C lq * (q.roots.map fun a => X - C a).prod) * C lp := by ring
      _ = q * C lp := by rw [← hqs]
  -- pick a good evaluation point and contradict ‖φ‖ > 1
  have hbad : ({w : ℂ | q.IsRoot w} ∪ {w : ℂ | (q.comp fpoly).IsRoot w}).Finite :=
    (finite_setOf_isRoot hq).union (finite_setOf_isRoot hqcomp)
  obtain ⟨w, hw⟩ := ((escapeOpen_infinite c).sdiff hbad).nonempty
  have hwesc : w ∈ escapeOpen c := hw.1
  have hwgood : w ∉ ({w : ℂ | q.IsRoot w} ∪ {w : ℂ | (q.comp fpoly).IsRoot w}) := hw.2
  have hqw : q.eval w ≠ 0 := fun h => hwgood (Or.inl h)
  have hqfw : q.eval (w ^ (2 : ℕ) + c) ≠ 0 := by
    intro h
    apply hwgood
    right
    show (q.comp fpoly).eval w = 0
    rw [eval_comp, hfeval]
    exact h
  obtain ⟨hcw, h2w⟩ := mem_escapeOpen_regime hwesc
  have hfw : quadratic c w ∈ escapeOpen c := quadratic_mem_escapeOpen hwesc
  have hlq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  -- φ(w)·lq = lp and φ(fw)·lq = lp
  have hval : ∀ v : ℂ, v ∈ escapeOpen c → q.eval v ≠ 0 →
      bottcherCoord c v * q.leadingCoeff = p.leadingCoeff := by
    intro v hv hqv
    have h1 := hrat v hv
    have h2 := congrArg (fun r => Polynomial.eval v r) hprop
    simp only [eval_mul, eval_C] at h2
    have h3 : q.eval v * (bottcherCoord c v * q.leadingCoeff)
        = q.eval v * p.leadingCoeff := by
      calc q.eval v * (bottcherCoord c v * q.leadingCoeff)
          = (q.eval v * bottcherCoord c v) * q.leadingCoeff := by ring
        _ = p.eval v * q.leadingCoeff := by rw [h1]
        _ = q.eval v * p.leadingCoeff := h2
    exact mul_left_cancel₀ hqv h3
  have hv1 := hval w hwesc hqw
  have hv2 := hval _ hfw (by simpa [quadratic_apply] using hqfw)
  have hFE := bottcherCoord_quadratic hcw h2w
  rw [hFE] at hv2
  -- φ(w)² lq = φ(w) lq ⟹ φ(w) = 1 (φ ≠ 0, lq ≠ 0)
  have hφw : bottcherCoord c w = 1 := by
    have h1 : bottcherCoord c w ^ (2 : ℕ) * q.leadingCoeff
        = bottcherCoord c w * q.leadingCoeff := by
      calc bottcherCoord c w ^ (2 : ℕ) * q.leadingCoeff = p.leadingCoeff := hv2
        _ = bottcherCoord c w * q.leadingCoeff := hv1.symm
    have h2 : (bottcherCoord c w - 1) * (bottcherCoord c w * q.leadingCoeff) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · have := sub_eq_zero.mp h
      simpa using this
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (bottcherCoord_ne_zero c w)
      · exact absurd h' hlq
  have := one_lt_norm_bottcherCoord hcw h2w
  rw [hφw] at this
  simp at this

end BottcherNotRational
