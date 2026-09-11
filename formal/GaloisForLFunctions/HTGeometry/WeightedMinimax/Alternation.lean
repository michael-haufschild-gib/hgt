import GaloisForLFunctions.HTGeometry.WeightedMinimax.Perturbation
import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature

/-!
# The weighted alternation theorem

A monic minimizer of the weighted supremum on `Icc a b` has at least `n+1` extreme points at which
the polynomial alternates in sign. The proof combines three inputs, none of them assumed:

* the improving perturbation (`exists_sign_mismatch_of_minimizer`): no polynomial of degree `< n`
  matches the sign of `T` at every extreme point;
* strict separation in `ℝ^n` together with the corpus's finite atomic cubature
  (`exists_atomic_of_mem_closure_convexHull`): consequently the weighted monomial-moment vectors of
  the extreme points admit `0` as a genuine finite convex combination;
* the finite sign-realization lemma (`exists_sign_realizing`): a vanishing such combination forces
  at least `n` sign alternations among the chosen points.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Set Polynomial

variable {v : ℝ → ℝ} {a b : ℝ}

/-! ### Coefficient vectors and polynomials of degree `< n` -/

/-- The polynomial of degree `< n` with coefficient vector `α`. -/
def polyOfVec (n : ℕ) (α : Fin n → ℝ) : Polynomial ℝ :=
  ∑ j : Fin n, Polynomial.C (α j) * Polynomial.X ^ (j : ℕ)

theorem polyOfVec_coeff_eq_zero (n : ℕ) (α : Fin n → ℝ) {i : ℕ} (h : n ≤ i) :
    (polyOfVec n α).coeff i = 0 := by
  unfold polyOfVec
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (i = (j : ℕ))),
    mul_zero]

theorem polyOfVec_eval (n : ℕ) (α : Fin n → ℝ) (x : ℝ) :
    (polyOfVec n α).eval x = ∑ j : Fin n, α j * x ^ (j : ℕ) := by
  unfold polyOfVec
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun j _ => by simp)

/-- The `j`-th weighted monomial moment of a point, signed by the value of `T`. -/
def momentVec (v : ℝ → ℝ) (T : Polynomial ℝ) (n : ℕ) (x : ℝ) : Fin n → ℝ :=
  fun j => T.eval x * v x * x ^ (j : ℕ)

theorem momentVec_continuous (hv : Continuous v) (T : Polynomial ℝ) (n : ℕ) :
    Continuous (momentVec v T n) := by
  refine continuous_pi (fun j => ?_)
  exact (((Polynomial.continuous T).mul hv).mul (continuous_pow (j : ℕ)))

theorem clm_apply_eq_sum {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (y : Fin n → ℝ) :
    f y = ∑ j : Fin n, y j * f (Pi.single j 1) := by
  have hy : ∑ j : Fin n, y j • (Pi.single j (1:ℝ)) = y := by
    have hs : ∀ j : Fin n, y j • (Pi.single j (1:ℝ)) = Pi.single j (y j) := by
      intro j
      ext k
      simp [Pi.single_apply]
    simp only [hs]
    exact Finset.univ_sum_single y
  calc f y = f (∑ j : Fin n, y j • (Pi.single j (1:ℝ))) := by rw [hy]
    _ = ∑ j : Fin n, y j * f (Pi.single j 1) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])

/-! ### The origin is a finite convex combination of the signed moment vectors -/

theorem zero_mem_closure_convexHull_momentVec (hw : IsWeight v a b) {n : ℕ} {T : Polynomial ℝ}
    (hT : T ∈ monicDeg n) (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) :
    (0 : Fin n → ℝ) ∈
      closure (convexHull ℝ (momentVec v T n '' extremeSet v a b T)) := by
  by_contra hcon
  obtain ⟨f, u, hf0, hfy⟩ := geometric_hahn_banach_point_closed
    ((convex_convexHull ℝ (momentVec v T n '' extremeSet v a b T)).closure) isClosed_closure hcon
  have hTne : T ≠ 0 := by
    intro h
    have h2 := hT.2
    rw [h] at h2
    simp at h2
  set α : Fin n → ℝ := fun j => f (Pi.single j 1) with hα
  have hstrict : ∀ x ∈ extremeSet v a b T, 0 < T.eval x * (polyOfVec n α).eval x := by
    intro x hx
    have hmem : momentVec v T n x ∈
        closure (convexHull ℝ (momentVec v T n '' extremeSet v a b T)) :=
      subset_closure (subset_convexHull ℝ _ ⟨x, hx, rfl⟩)
    have h1 : u < f (momentVec v T n x) := hfy _ hmem
    have h2 : f (momentVec v T n x) = T.eval x * v x * (polyOfVec n α).eval x := by
      rw [clm_apply_eq_sum, polyOfVec_eval, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show momentVec v T n x j * α j = T.eval x * v x * (α j * x ^ (j : ℕ))
      unfold momentVec
      ring
    have h3 : (0:ℝ) < T.eval x * v x * (polyOfVec n α).eval x := by
      have h4 : f (0 : Fin n → ℝ) = 0 := by simp
      rw [h4] at hf0
      rw [← h2]
      linarith
    obtain ⟨hv0, _⟩ := pos_of_mem_extremeSet hw hTne hx
    have h5 : 0 < v x * (T.eval x * (polyOfVec n α).eval x) := by nlinarith
    by_contra hcc
    push Not at hcc
    nlinarith
  obtain ⟨x, hx, hle⟩ := exists_sign_mismatch_of_minimizer hw hT hmin
    (g := polyOfVec n α) (fun i hi => polyOfVec_coeff_eq_zero n α hi)
  exact absurd (hstrict x hx) (not_lt.mpr hle)

/-! ### The alternation theorem -/

/-- **Weighted alternation.** A monic minimizer of degree `n` has `n+1` extreme points at which it
alternates in sign. -/
theorem exists_alternating_extreme_chain (hw : IsWeight v a b) {n : ℕ} {T : Polynomial ℝ}
    (hT : T ∈ monicDeg n) (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) :
    ∃ z : ℕ → ℝ, (∀ i < n, z i < z (i + 1)) ∧ (∀ i ≤ n, z i ∈ extremeSet v a b T) ∧
      (∀ i < n, T.eval (z i) * T.eval (z (i + 1)) < 0) := by
  classical
  have hTne : T ≠ 0 := by
    intro h
    have h2 := hT.2
    rw [h] at h2
    simp at h2
  set E := extremeSet v a b T with hE
  have hEcpt : IsCompact E := extremeSet_isCompact hw T
  have hEne : E.Nonempty := extremeSet_nonempty hw T
  have hScpt : IsCompact (momentVec v T n '' E) :=
    hEcpt.image (momentVec_continuous hw.cont T n)
  have hSne : (momentVec v T n '' E).Nonempty := hEne.image _
  obtain ⟨w, zz, hw0, hw1, hzS, hzsum⟩ := exists_atomic_of_mem_closure_convexHull
    hScpt hSne (zero_mem_closure_convexHull_momentVec hw hT hmin)
  have hpt : ∀ i : Fin (n + 1), ∃ y ∈ E, momentVec v T n y = zz i := by
    intro i
    obtain ⟨y, hy, hyz⟩ := hzS i
    exact ⟨y, hy, hyz⟩
  choose pt hptE hptz using hpt
  -- coordinatewise vanishing
  have hcoord : ∀ j : Fin n, ∑ i : Fin (n + 1), w i * (T.eval (pt i) * v (pt i) * (pt i) ^ (j:ℕ))
      = 0 := by
    intro j
    have h1 : (∑ i : Fin (n + 1), w i • zz i) j = (0 : Fin n → ℝ) j := by rw [hzsum]
    rw [Finset.sum_apply] at h1
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h1
    calc ∑ i : Fin (n + 1), w i * (T.eval (pt i) * v (pt i) * (pt i) ^ (j:ℕ))
        = ∑ i : Fin (n + 1), w i * zz i j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← hptz i]
          rfl
      _ = 0 := h1
  -- group the atoms by their location
  set I : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => 0 < w i) with hI
  have hIne : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hz : ∀ i : Fin (n + 1), w i = 0 := by
      intro i
      have : i ∉ I := by rw [hne]; simp
      rw [hI, Finset.mem_filter] at this
      simp only [Finset.mem_univ, true_and, not_lt] at this
      exact le_antisymm this (hw0 i)
    rw [Finset.sum_congr rfl (fun i _ => hz i)] at hw1
    simp at hw1
  set X : Finset ℝ := I.image pt with hX
  have hXne : X.Nonempty := hIne.image _
  have hXE : ∀ y ∈ X, y ∈ E := by
    intro y hy
    rw [hX, Finset.mem_image] at hy
    obtain ⟨i, _, rfl⟩ := hy
    exact hptE i
  set W : ℝ → ℝ := fun y => ∑ i ∈ I.filter (fun i => pt i = y), w i with hW
  set mu : ℝ → ℝ := fun y => W y * (T.eval y * v y) with hmu
  have hWpos : ∀ y ∈ X, 0 < W y := by
    intro y hy
    rw [hX, Finset.mem_image] at hy
    obtain ⟨i, hiI, rfl⟩ := hy
    refine Finset.sum_pos' (fun k hk => ?_) ⟨i, ?_, ?_⟩
    · have := (Finset.mem_filter.mp hk).1
      rw [hI, Finset.mem_filter] at this
      exact this.2.le
    · exact Finset.mem_filter.mpr ⟨hiI, rfl⟩
    · rw [hI, Finset.mem_filter] at hiI
      exact hiI.2
  have hmune : ∀ y ∈ X, mu y ≠ 0 := by
    intro y hy
    obtain ⟨hv0, hT0⟩ := pos_of_mem_extremeSet hw hTne (hXE y hy)
    have := hWpos y hy
    rw [hmu]
    exact mul_ne_zero (ne_of_gt this) (mul_ne_zero hT0 (ne_of_gt hv0))
  -- the grouped moments vanish
  have hmom : ∀ j : ℕ, j < n → ∑ y ∈ X, mu y * y ^ j = 0 := by
    intro j hj
    have hmaps : ∀ i ∈ I, pt i ∈ X := by
      intro i hi
      rw [hX]
      exact Finset.mem_image_of_mem pt hi
    have hfib := Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => w i * (T.eval (pt i) * v (pt i) * (pt i) ^ j))
    have hfull : ∑ i ∈ I, w i * (T.eval (pt i) * v (pt i) * (pt i) ^ j)
        = ∑ i : Fin (n + 1), w i * (T.eval (pt i) * v (pt i) * (pt i) ^ j) := by
      refine Finset.sum_subset (Finset.subset_univ I) ?_
      intro i _ hi
      rw [hI, Finset.mem_filter] at hi
      simp only [Finset.mem_univ, true_and, not_lt] at hi
      rw [le_antisymm hi (hw0 i), zero_mul]
    have hinner : ∀ y ∈ X, ∑ i ∈ I.filter (fun i => pt i = y),
        w i * (T.eval (pt i) * v (pt i) * (pt i) ^ j) = mu y * y ^ j := by
      intro y _
      simp only [hmu, hW]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [(Finset.mem_filter.mp hi).2]
      ring
    rw [Finset.sum_congr rfl hinner] at hfib
    rw [hfib, hfull]
    exact hcoord ⟨j, hj⟩
  have hgsum : ∀ g : Polynomial ℝ, g.natDegree < n → ∑ y ∈ X, mu y * g.eval y = 0 := by
    intro g hg
    have hstep : ∑ y ∈ X, mu y * g.eval y
        = ∑ y ∈ X, ∑ i ∈ Finset.range n, g.coeff i * (mu y * y ^ i) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Polynomial.eval_eq_sum_range' hg y, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [← Finset.mul_sum, hmom i (Finset.mem_range.mp hi), mul_zero]
  -- enumerate `X` in increasing order
  obtain ⟨xx, L, hxmono, hxmem, hxsurj, _⟩ := exists_monotone_enumeration X hXne
  obtain ⟨k, g, idx, hdeg, hnodes, _, hmono, hle, hidxk, halt⟩ :=
    exists_sign_realizing xx (fun i => mu (xx i)) L hxmono
    (fun i hi => hmune (xx i) (hxmem i hi))
  have hkn : n ≤ k := by
    by_contra hkn
    have hgn : g.natDegree < n := lt_of_le_of_lt hdeg (by omega)
    have hzero := hgsum g hgn
    have hpos : 0 < ∑ y ∈ X, mu y * g.eval y := by
      refine Finset.sum_pos (fun y hy => ?_) hXne
      obtain ⟨i, hi, rfl⟩ := hxsurj y hy
      exact hnodes i hi
    exact absurd hzero (ne_of_gt hpos)
  refine ⟨fun i => xx (idx i), ?_, ?_, ?_⟩
  · intro i hi
    have h1 : idx i < idx (i + 1) := hmono i (by omega)
    have h2 : idx (i + 1) ≤ L := hle (i + 1) (by omega)
    exact step_mono_lt hxmono h1 h2
  · intro i hi
    exact hXE _ (hxmem _ (hle i (by omega)))
  · intro i hi
    have h1 := halt i (by omega)
    have hyi := hxmem (idx i) (hle i (by omega))
    have hyi1 := hxmem (idx (i + 1)) (hle (i + 1) (by omega))
    obtain ⟨hv1, hT1⟩ := pos_of_mem_extremeSet hw hTne (hXE _ hyi)
    obtain ⟨hv2, hT2⟩ := pos_of_mem_extremeSet hw hTne (hXE _ hyi1)
    have hW1 := hWpos _ hyi
    have hW2 := hWpos _ hyi1
    simp only [hmu] at h1
    have hkey : 0 < (W (xx (idx i)) * v (xx (idx i))) * (W (xx (idx (i + 1))) * v (xx (idx (i + 1)))) :=
      mul_pos (mul_pos hW1 hv1) (mul_pos hW2 hv2)
    by_contra hc
    push Not at hc
    nlinarith [h1, mul_nonneg (le_of_lt hkey) hc]

end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
