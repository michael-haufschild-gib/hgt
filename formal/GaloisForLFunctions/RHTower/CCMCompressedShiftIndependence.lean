import GaloisForLFunctions.Core
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Topology.Algebra.Support

/-!
# Compressed weighted prime shifts are linearly independent

The weighted bilateral translation `S h f x = e^h * f (x - h)` is a one-parameter semigroup.
Compressing it to an aperture window,

```text
T A h f = 1_[0,A] * (fun x => e^h * (1_[0,A] * f) (x - h)),
```

produces the family of operators carrying the arithmetic directions `h = log n`.  Two independence
theorems are proved here.

* `linearIndependent_compressedShift` — for any injective family of shifts inside `[0, A)` the
  compressed operators are linearly independent.  The witness is an indicator of a short interval
  whose translates by the different shifts are pairwise disjoint; the interval length is chosen per
  coefficient, so no monotonicity of the shifts is needed.
* `linearIndependent_weightedShift_apply` — the pointed cyclic strengthening: for a **single**
  nonzero compactly supported vector the translates `S (h j) f` are already independent.  The proof
  replaces the Fourier argument by the rightmost point of the support: at the largest shift with a
  nonzero coefficient every other term has already left the support.

Together with `GaloisForLFunctions.linearIndependent_log_primes` this gives the faithfulness of the
prime-log carrier: distinct prime logarithms below the aperture give independent compressed shifts,
so the operator span is a faithful copy of the prime-log space.

The last section records the Krein block identity: with weights `a n ≥ 0` and the two feature maps
`√(a n) (T n f ± c f)`, the difference of squared norms is `4 c` times the weighted real part of the
diagonal pairings.  This is the parallelogram identity behind the source-defined indefinite
factorization.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set

/-! ## The weighted shift and its compression -/

/-- The weighted bilateral translation `S h f x = e^h * f (x - h)`. -/
def weightedShift (h : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => (Real.exp h : ℂ) * f (x - h)
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp [smul_eq_mul]; ring

theorem weightedShift_apply (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    weightedShift h f x = (Real.exp h : ℂ) * f (x - h) := rfl

/-- **The semigroup law.** -/
theorem weightedShift_comp (h k : ℝ) (f : ℝ → ℂ) :
    weightedShift h (weightedShift k f) = weightedShift (h + k) f := by
  funext x
  simp only [weightedShift_apply, Real.exp_add, Complex.ofReal_mul]
  rw [show x - h - k = x - (h + k) from by ring]
  ring

/-- The aperture compression of the weighted shift. -/
def compressedShift (A h : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x =>
    if x ∈ Icc (0 : ℝ) A then
      (Real.exp h : ℂ) * (if x - h ∈ Icc (0 : ℝ) A then f (x - h) else 0)
    else 0
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem compressedShift_apply (A h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    compressedShift A h f x =
      if x ∈ Icc (0 : ℝ) A then
        (Real.exp h : ℂ) * (if x - h ∈ Icc (0 : ℝ) A then f (x - h) else 0)
      else 0 := rfl

/-! ## Independence of the compressed shifts -/

/-- **The compressed weighted shifts of an injective family of shifts inside `[0, A)` are linearly
independent.**  The separating witness is an indicator of a short interval; its length is chosen
after fixing the coefficient to be isolated, so no ordering of the shifts is required. -/
theorem linearIndependent_compressedShift {r : ℕ} {A : ℝ} {h : Fin r → ℝ}
    (hinj : Function.Injective h) (hnn : ∀ j, 0 ≤ h j) (hlt : ∀ j, h j < A) :
    LinearIndependent ℂ (fun j : Fin r => compressedShift A (h j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum j₀
  -- pointwise form of the relation
  have happ : ∀ (f : ℝ → ℂ) (x : ℝ), ∑ j, c j * compressedShift A (h j) f x = 0 := by
    intro f x
    have h1 : (∑ j, c j • compressedShift A (h j)) f x = 0 := by rw [hsum]; simp
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h1
  -- a separation scale for `j₀`
  set g : Fin r → ℝ := fun j => if j = j₀ then A - h j₀ else |h j - h j₀| with hg
  have hgpos : ∀ j, 0 < g j := by
    intro j
    by_cases hj : j = j₀
    · simp only [hg, hj, if_pos rfl]
      linarith [hlt j₀]
    · simp only [hg, if_neg hj]
      exact abs_pos.mpr (sub_ne_zero.mpr fun heq => hj (hinj heq))
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
  set m : ℝ := Finset.univ.inf' hne g with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    exact fun j _ => hgpos j
  set ε : ℝ := m / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hεlt : ∀ j, ε < g j := by
    intro j
    have : m ≤ g j := Finset.inf'_le g (Finset.mem_univ j)
    rw [hε]; linarith
  -- the separating witness and the evaluation point
  set f : ℝ → ℂ := fun y => if y ∈ Icc (0 : ℝ) ε then 1 else 0 with hf
  set x : ℝ := h j₀ + ε / 2 with hx
  have hxmem : x ∈ Icc (0 : ℝ) A := by
    constructor
    · rw [hx]; linarith [hnn j₀]
    · have := hεlt j₀
      simp only [hg, if_pos rfl] at this
      rw [hx]; linarith
  have hj₀mem : x - h j₀ ∈ Icc (0 : ℝ) A := by
    rw [hx]
    constructor
    · linarith
    · have := hεlt j₀
      simp only [hg, if_pos rfl] at this
      have := hnn j₀
      simp only [add_sub_cancel_left]
      linarith
  -- the isolated term
  have hterm : compressedShift A (h j₀) f x = (Real.exp (h j₀) : ℂ) := by
    rw [compressedShift_apply, if_pos hxmem, if_pos hj₀mem, hf]
    have hy : x - h j₀ ∈ Icc (0 : ℝ) ε := by
      rw [hx]
      simp only [add_sub_cancel_left]
      exact ⟨by linarith, by linarith⟩
    simp only [if_pos hy, mul_one]
  -- the other terms vanish
  have hother : ∀ j, j ≠ j₀ → compressedShift A (h j) f x = 0 := by
    intro j hj
    have hgap : ε < |h j - h j₀| := by
      have := hεlt j
      simpa [hg, if_neg hj] using this
    rw [compressedShift_apply, if_pos hxmem, hf]
    have hout : x - h j ∉ Icc (0 : ℝ) ε := by
      rcases lt_or_gt_of_ne (fun heq : h j = h j₀ => hj (hinj heq)) with hlt' | hgt'
      · -- `h j < h j₀`, so `x - h j` overshoots `ε`
        have hgap' : ε < h j₀ - h j := by
          rw [abs_of_neg (by linarith : h j - h j₀ < 0)] at hgap
          linarith
        intro hmem
        have h2 := hmem.2
        rw [hx] at h2
        linarith
      · -- `h j > h j₀`, so `x - h j` is negative
        have hgap' : ε < h j - h j₀ := by
          rw [abs_of_pos (by linarith : (0 : ℝ) < h j - h j₀)] at hgap
          linarith
        intro hmem
        have h1 := hmem.1
        rw [hx] at h1
        linarith
    by_cases hIcc : x - h j ∈ Icc (0 : ℝ) A
    · simp only [if_pos hIcc, if_neg hout, mul_zero]
    · simp only [if_neg hIcc, mul_zero]
  -- conclude
  have hzero := happ f x
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hother j hj, mul_zero])
    (fun hj => absurd (Finset.mem_univ j₀) hj), hterm] at hzero
  have hexp : (Real.exp (h j₀) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  exact (mul_eq_zero.mp hzero).resolve_right hexp

/-! ## Faithfulness of the prime-log carrier -/

/-- **Distinct prime logarithms below the aperture give independent compressed shifts.**  Together
with the `ℚ`-linear independence of prime logarithms this is the faithfulness of the prime-log
operator carrier. -/
theorem linearIndependent_compressedShift_primes {A : ℝ} {r : ℕ} {p : Fin r → Nat.Primes}
    (hpinj : Function.Injective p) (hA : ∀ j, ((p j : ℕ) : ℝ) < Real.exp A) :
    LinearIndependent ℂ (fun j : Fin r => compressedShift A (Real.log ((p j : ℕ) : ℝ))) := by
  have hpos : ∀ j, (1 : ℝ) < ((p j : ℕ) : ℝ) := by
    intro j
    have h2 : 2 ≤ (p j : ℕ) := (p j).2.two_le
    have : (2 : ℝ) ≤ ((p j : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  refine linearIndependent_compressedShift (h := fun j => Real.log ((p j : ℕ) : ℝ)) ?_ ?_ ?_
  · intro i j hij
    have hp : ((p i : ℕ) : ℝ) = ((p j : ℕ) : ℝ) := by
      have hi := (hpos i).trans_le le_rfl
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith [hpos i]))
        (Set.mem_Ioi.mpr (by linarith [hpos j])) hij
    have : (p i : ℕ) = (p j : ℕ) := by exact_mod_cast hp
    exact hpinj (Subtype.ext this)
  · intro j
    exact Real.log_nonneg (hpos j).le
  · intro j
    have := hA j
    calc Real.log ((p j : ℕ) : ℝ) < Real.log (Real.exp A) :=
          Real.log_lt_log (by linarith [hpos j]) this
      _ = A := Real.log_exp A

/-! ## Independence on one cyclic vector -/

/-- **The pointed cyclic strengthening.**  For a single nonzero compactly supported vector the
weighted translates by distinct shifts are already linearly independent.  At the largest shift with a
nonzero coefficient, every other term has left the support. -/
theorem linearIndependent_weightedShift_apply {r : ℕ} {h : Fin r → ℝ}
    (hinj : Function.Injective h) {f : ℝ → ℂ} (hf : f ≠ 0) (hcs : HasCompactSupport f) :
    LinearIndependent ℂ (fun j : Fin r => weightedShift (h j) f) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨jbad, hjbad⟩ := hcon
  -- the coefficient support
  set S : Finset (Fin r) := Finset.univ.filter fun j => c j ≠ 0 with hS
  have hSne : S.Nonempty := ⟨jbad, by simp [hS, hjbad]⟩
  obtain ⟨j₀, hj₀S, hj₀max⟩ := S.exists_max_image h hSne
  -- the rightmost point of the support
  have hsupp : (Function.support f).Nonempty := by
    rcases Function.ne_iff.mp hf with ⟨y, hy⟩
    exact ⟨y, hy⟩
  have hbdd : BddAbove (Function.support f) := by
    have hc : IsCompact (tsupport f) := hcs
    exact hc.bddAbove.mono (subset_tsupport f)
  set M : ℝ := sSup (Function.support f) with hM
  -- a gap below the maximal shift
  set g : Fin r → ℝ := fun j => if j = j₀ then 1 else h j₀ - h j with hg
  have hgpos : ∀ j ∈ S, 0 < g j := by
    intro j hjS
    by_cases hj : j = j₀
    · simp only [hg, hj, if_pos rfl]; norm_num
    · simp only [hg, if_neg hj]
      have hle := hj₀max j hjS
      have hne : h j ≠ h j₀ := fun heq => hj (hinj heq)
      cases lt_or_eq_of_le hle with
      | inl hlt => linarith
      | inr heq => exact absurd heq hne
  set δ : ℝ := (S.inf' hSne g) / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : 0 < S.inf' hSne g := by
      rw [Finset.lt_inf'_iff]
      exact hgpos
    linarith
  have hδlt : ∀ j ∈ S, δ < g j := by
    intro j hjS
    have : S.inf' hSne g ≤ g j := Finset.inf'_le g hjS
    rw [hδ]
    have hpos : 0 < S.inf' hSne g := by rw [Finset.lt_inf'_iff]; exact hgpos
    linarith
  -- a support point close to the top
  obtain ⟨y, hyS, hylt⟩ : ∃ y ∈ Function.support f, M - δ < y := by
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    have : M ≤ M - δ := csSup_le hsupp fun y hy => hno y hy
    linarith
  have hyle : y ≤ M := le_csSup hbdd hyS
  set x : ℝ := y + h j₀ with hx
  -- evaluate
  have happ : ∑ j, c j * weightedShift (h j) f x = 0 := by
    have h1 : (∑ j, c j • weightedShift (h j) f) x = 0 := by rw [hsum]; simp
    simpa [Finset.sum_apply, smul_eq_mul] using h1
  have hother : ∀ j, j ≠ j₀ → c j * weightedShift (h j) f x = 0 := by
    intro j hj
    by_cases hjS : j ∈ S
    · have hgap : δ < h j₀ - h j := by
        have := hδlt j hjS
        simpa [hg, if_neg hj] using this
      have hout : x - h j ∉ Function.support f := by
        intro hmem
        have hle := le_csSup hbdd hmem
        rw [hx] at hle
        linarith
      rw [weightedShift_apply, Function.notMem_support.mp hout, mul_zero, mul_zero]
    · have : c j = 0 := by
        by_contra hcj
        exact hjS (by simp [hS, hcj])
      rw [this, zero_mul]
  rw [Finset.sum_eq_single j₀ (fun j _ hj => hother j hj)
    (fun hj => absurd (Finset.mem_univ j₀) hj)] at happ
  have hcj₀ : c j₀ ≠ 0 := by
    have := hj₀S
    simp [hS] at this
    exact this
  have hfy : f (y + h j₀ - h j₀) ≠ 0 := by
    simp only [add_sub_cancel_right]
    exact hyS
  rw [weightedShift_apply, hx] at happ
  have hexp : (Real.exp (h j₀) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rcases mul_eq_zero.mp happ with hc | hrest
  · exact hcj₀ hc
  · rcases mul_eq_zero.mp hrest with he | hz
    · exact hexp he
    · exact hfy hz

/-! ## The Krein block identity -/

/-- **The Krein block identity.**  With nonnegative weights and the two feature maps
`√(a n) (T n f ± c f)`, the difference of squared norms is `4c` times the weighted real part of the
diagonal pairings.  This is the parallelogram identity underlying the indefinite factorization of the
completed finite-aperture form. -/
theorem kreinBlock_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (T : ι → E) (v : E) (c : ℝ) :
    (∑ n ∈ s, a n * ‖T n + (c : ℂ) • v‖ ^ 2) - (∑ n ∈ s, a n * ‖T n - (c : ℂ) • v‖ ^ 2)
      = 4 * c * ∑ n ∈ s, a n * RCLike.re (inner ℂ (T n) v) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hplus : ‖T n + (c : ℂ) • v‖ ^ 2
      = ‖T n‖ ^ 2 + 2 * RCLike.re (inner ℂ (T n) ((c : ℂ) • v)) + ‖(c : ℂ) • v‖ ^ 2 :=
    norm_add_sq _ _
  have hminus : ‖T n - (c : ℂ) • v‖ ^ 2
      = ‖T n‖ ^ 2 - 2 * RCLike.re (inner ℂ (T n) ((c : ℂ) • v)) + ‖(c : ℂ) • v‖ ^ 2 :=
    norm_sub_sq _ _
  have hinner : RCLike.re (inner ℂ (T n) ((c : ℂ) • v)) = c * RCLike.re (inner ℂ (T n) v) := by
    rw [inner_smul_right]
    simp
  rw [hplus, hminus, hinner]
  ring

end GaloisForLFunctions.RHTower

end
