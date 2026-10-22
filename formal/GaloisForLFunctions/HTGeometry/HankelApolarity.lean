import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelDiagonalMonicity

/-!
# Apolarity for finite moment sequences

A point `x ∈ L^N` is read as the moment functional `Λ(f) = Σ_{k<N} f_k x_k` on polynomials.  A row
vector `(g_0, …, g_r)` of the `(r+1)`-row Hankel matrix `(x_{i+j})` is the polynomial
`g = Σ g_i T^i`, and it lies in the left kernel exactly when `Λ(g T^j) = 0` for every column `j`:
`g` *annihilates the window*.

* `annihilatesWindow_extend` — **Krylov**: if a polynomial `g` of exact degree `r` annihilates the
  long window and `w` of degree `< r` annihilates the first `r` columns, then `w` annihilates the
  whole window, by dividing `T^j` by `g`.
* `momentFunctional_chartPoint` — translating the measure by `t` and reversing the window turns
  `Λ` into `f ↦ Λ((reflect f)(T + t))`.
* `exists_chart_det_ne_zero` — **the moved charts cover the rank-`r` locus**: if every maximal
  `(r+1)`-minor vanishes at `x` and some maximal `r`-minor does not, then for some `t ≤ r` the
  leading `r × r` Hankel minor of the moved point is nonzero.  The left-kernel polynomial `g` has at
  most `r` roots; at `t` with `g(−t) ≠ 0` the moved kernel polynomial has exact degree `r`, and the
  Krylov step forces the leading block to be invertible.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {L : Type*} [Field L] {N : ℕ}

/-- The moment functional `f ↦ Σ_{k<N} x_k f_k`. -/
def momentFunctional (x : Fin N → L) : L[X] →ₗ[L] L :=
  ∑ k : Fin N, x k • Polynomial.lcoeff L k

theorem momentFunctional_apply (x : Fin N → L) (f : L[X]) :
    momentFunctional x f = ∑ k : Fin N, x k * f.coeff k := by
  simp [momentFunctional, LinearMap.sum_apply]

theorem momentFunctional_C_mul (x : Fin N → L) (a : L) (f : L[X]) :
    momentFunctional x (C a * f) = a * momentFunctional x f := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem momentFunctional_C_mul_X_pow (x : Fin N → L) (a : L) {n : ℕ} (hn : n < N) :
    momentFunctional x (C a * X ^ n) = a * x ⟨n, hn⟩ := by
  classical
  rw [momentFunctional_C_mul, momentFunctional_apply, Finset.sum_eq_single ⟨n, hn⟩]
  · rw [coeff_X_pow_self, mul_one]
  · intro k _ hk
    rw [coeff_X_pow, if_neg (fun h => hk (Fin.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `g` annihilates the window of columns `0, …, m`. -/
def AnnihilatesWindow (x : Fin N → L) (g : L[X]) (m : ℕ) : Prop :=
  ∀ j ≤ m, momentFunctional x (g * X ^ j) = 0

theorem AnnihilatesWindow.mono {x : Fin N → L} {g : L[X]} {m m' : ℕ}
    (h : AnnihilatesWindow x g m) (hm : m' ≤ m) : AnnihilatesWindow x g m' :=
  fun j hj => h j (hj.trans hm)

theorem AnnihilatesWindow.mul {x : Fin N → L} {g : L[X]} {m : ℕ} (h : AnnihilatesWindow x g m)
    {u : L[X]} (hu : u.natDegree ≤ m) : momentFunctional x (g * u) = 0 := by
  rw [u.as_sum_range' (m + 1) (by omega), Finset.mul_sum, map_sum]
  simp_rw [← C_mul_X_pow_eq_monomial]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [mul_left_comm, momentFunctional_C_mul, h i (by have := Finset.mem_range.mp hi; omega),
    mul_zero]

/-- Change of variable inside an annihilated window: powers of `P` may be replaced by powers of
`P + s`. -/
theorem momentFunctional_mul_add_C_pow (x : Fin N → L) (h P : L[X]) (m : ℕ)
    (hP : ∀ k ≤ m, momentFunctional x (h * P ^ k) = 0) (s : L) :
    ∀ k ≤ m, momentFunctional x (h * (P + C s) ^ k) = 0 := by
  intro k hk
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show h * (P ^ i * C s ^ (k - i) * (k.choose i : L[X])) =
      C (s ^ (k - i) * (k.choose i : L)) * (h * P ^ i) by
    rw [C_mul, C_pow, ← map_natCast C]; ring]
  rw [momentFunctional_C_mul, hP i (hi'.trans hk), mul_zero]

/-! ## The Krylov step -/

/-- **Krylov.**  Let `g` have exact degree `r` and annihilate the window `0, …, N−1−r`, and let `w`
of degree `< r` annihilate the first `r` columns.  Then `w` annihilates `0, …, N−r`. -/
theorem annihilatesWindow_extend (x : Fin N → L) {g w : L[X]} {r : ℕ} (hrN : 2 * r ≤ N)
    (hg : g.natDegree ≤ r) (hgr : g.coeff r ≠ 0) (hgw : AnnihilatesWindow x g (N - 1 - r))
    (hw : w.natDegree < r) (hw0 : AnnihilatesWindow x w (r - 1)) :
    AnnihilatesWindow x w (N - r) := by
  intro j hj
  have hg0 : g ≠ 0 := fun h => hgr (by rw [h, coeff_zero])
  have hgdeg : g.natDegree = r := natDegree_eq_of_le_of_coeff_ne_zero hg hgr
  have hlead : g.leadingCoeff = g.coeff r := by rw [leadingCoeff, hgdeg]
  set G := g * C g.leadingCoeff⁻¹ with hG
  have hGm : G.Monic := monic_mul_leadingCoeff_inv hg0
  have hGdeg : G.natDegree = r := by
    rw [hG, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)), hgdeg]
  have hsplit := modByMonic_add_div (X ^ j : L[X]) G
  have hexp : w * X ^ j = w * (X ^ j %ₘ G) + g * (C g.leadingCoeff⁻¹ * (w * (X ^ j /ₘ G))) := by
    conv_lhs => rw [← hsplit]
    rw [hG]; ring
  rw [hexp, map_add]
  have hr1 : 1 ≤ r := by omega
  have h1 : momentFunctional x (w * (X ^ j %ₘ G)) = 0 := by
    refine hw0.mul ?_
    have := natDegree_modByMonic_lt (X ^ j : L[X]) hGm
      (by intro h; rw [h, natDegree_one] at hGdeg; omega)
    rw [hGdeg] at this
    omega
  have h2 : momentFunctional x (g * (C g.leadingCoeff⁻¹ * (w * (X ^ j /ₘ G)))) = 0 := by
    refine hgw.mul ?_
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    rw [natDegree_divByMonic _ hGm, natDegree_X_pow, hGdeg]
    omega
  rw [h1, h2, add_zero]

/-! ## Moving the chart -/

/-- The point moved by reversal and translation by `t`: `y_n = Λ((T + t)^{N−1−n})`. -/
def chartPoint (x : Fin N → L) (t : L) : Fin N → L :=
  fun n => momentFunctional x ((X + C t) ^ (N - 1 - (n : ℕ)))

theorem natDegree_X_add_C_pow_le' (t : L) (n : ℕ) : ((X + C t) ^ n).natDegree ≤ n := by
  refine (natDegree_pow_le_of_le (m := 1) n ?_).trans (by rw [mul_one])
  refine (natDegree_add_le _ _).trans ?_
  rw [natDegree_C, max_le_iff]
  exact ⟨natDegree_X_le, zero_le_one⟩

theorem momentFunctional_chartPoint (x : Fin N → L) (t : L) {f : L[X]} (hf : f.natDegree ≤ N - 1) :
    momentFunctional (chartPoint x t) f = momentFunctional x ((reflect (N - 1) f).comp (X + C t)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [momentFunctional_apply]
  have hrefl : (reflect (N - 1) f).natDegree < N := by
    have := natDegree_reflect_le (N := N - 1) (p := f)
    rw [max_eq_left hf] at this
    omega
  rw [momentFunctional_apply, comp, eval₂_eq_sum_range' _ hrefl, map_sum,
    ← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [chartPoint, Fin.revPerm_apply, momentFunctional_C_mul, coeff_reflect, Fin.val_rev,
    revAt_le (by omega)]
  rw [mul_comm]
  have hn := n.isLt
  rw [show N - ((n : ℕ) + 1) = N - 1 - n by omega, show N - 1 - (N - 1 - (n : ℕ)) = n by omega]

theorem sub_C_comp_add_C (t : L) : (X - C t).comp (X + C t) = X := by
  simp [sub_comp]

theorem add_C_comp_sub_C (t : L) : (X + C t).comp (X - C t) = X := by
  simp [add_comp]

theorem natDegree_X_sub_C_le' (t : L) : (X - C t).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_C, max_le_iff]
  exact ⟨natDegree_X_le, zero_le_one⟩

theorem reflect_mul_X_pow {f : L[X]} {a b j : ℕ} (hf : f.natDegree ≤ a) (hj : j ≤ b) :
    reflect (a + b) (f * X ^ j) = reflect a f * X ^ (b - j) := by
  rw [reflect_mul f (X ^ j) hf ((natDegree_X_pow_le j).trans hj), reflect_monomial, revAt_le hj]

/-- **The moved charts cover the rank-`r` locus**, at the level of points.  If every polynomial of
degree `≤ r` killing the long window is a multiple of nothing — i.e. some nonzero `g` of degree
`≤ r` annihilates `0, …, N−1−r` — while no nonzero polynomial of degree `< r` annihilates
`0, …, N−r`, then for some `t ≤ r` no nonzero polynomial of degree `< r` annihilates the first `r`
columns of the moved point. -/
theorem exists_chartPoint_injective [CharZero L] (x : Fin N → L) {r : ℕ} (hrN : 2 * r < N)
    (h1 : ∃ g : L[X], g ≠ 0 ∧ g.natDegree ≤ r ∧ AnnihilatesWindow x g (N - 1 - r))
    (h2 : ∀ h : L[X], h.natDegree < r → AnnihilatesWindow x h (N - r) → h = 0) :
    ∃ t ∈ Finset.range (r + 1), ∀ w : L[X], w.natDegree < r →
      AnnihilatesWindow (chartPoint x (t : L)) w (r - 1) → w = 0 := by
  classical
  obtain ⟨g, hg0, hgdeg, hgw⟩ := h1
  -- a translation at which `g` does not vanish
  obtain ⟨t, ht, hgt⟩ : ∃ t ∈ Finset.range (r + 1), g.eval (-(t : L)) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.range (r + 1)).image (fun t : ℕ => -(t : L)) ⊆ g.roots.toFinset := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      rw [Multiset.mem_toFinset, mem_roots hg0]
      exact hall t ht
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b h => by
      have : (a : L) = b := neg_injective h
      exact_mod_cast this), Finset.card_range] at hcard
    have := (Multiset.toFinset_card_le g.roots).trans (card_roots' g)
    omega
  refine ⟨t, ht, fun w hw hw0 => ?_⟩
  set y := chartPoint x (t : L) with hy
  have hr1 : 1 ≤ r := by omega
  -- the moved kernel polynomial has exact degree `r`
  set g' := g.comp (X - C (t : L)) with hg'
  have hg'deg : g'.natDegree ≤ r := by
    refine natDegree_comp_le.trans ?_
    have := Nat.mul_le_mul hgdeg (natDegree_X_sub_C_le' (t : L))
    omega
  set G := reflect r g' with hG
  have hGdeg : G.natDegree ≤ r := by
    have := natDegree_reflect_le (N := r) (p := g')
    rwa [max_eq_left hg'deg] at this
  have hGr : G.coeff r ≠ 0 := by
    rw [hG, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero, hg', eval_comp]
    simpa using hgt
  have hGw : AnnihilatesWindow y G (N - 1 - r) := by
    intro j hj
    have hdeg : (G * X ^ j).natDegree ≤ N - 1 := by
      refine natDegree_mul_le.trans ?_
      have := natDegree_X_pow_le (R := L) j
      omega
    rw [hy, momentFunctional_chartPoint x _ hdeg]
    rw [show N - 1 = r + (N - 1 - r) by omega, reflect_mul_X_pow hGdeg hj, hG, reflect_reflect,
      mul_comp, X_pow_comp, hg', comp_assoc]
    rw [sub_C_comp_add_C, comp_X]
    exact hgw.mul ((natDegree_X_add_C_pow_le' _ _).trans (by omega))
  -- Krylov in the moved coordinates
  have hwy := annihilatesWindow_extend y (by omega) hGdeg hGr hGw hw hw0
  -- back to `x`
  set h := (reflect (r - 1) w).comp (X + C (t : L)) with hh
  have hhdeg : h.natDegree < r := by
    refine lt_of_le_of_lt natDegree_comp_le ?_
    have h1 : (X + C (t : L)).natDegree ≤ 1 := by
      have := natDegree_X_add_C_pow_le' (t : L) 1
      rwa [pow_one] at this
    have h2 := natDegree_reflect_le (N := r - 1) (p := w)
    have h3 : (reflect (r - 1) w).natDegree ≤ r - 1 := by
      rwa [max_eq_left (by omega)] at h2
    have := Nat.mul_le_mul h3 h1
    omega
  have hhx : ∀ k ≤ N - r, momentFunctional x (h * (X + C (t : L)) ^ k) = 0 := by
    intro k hk
    have hj : N - r - k ≤ N - r := Nat.sub_le _ _
    have hdeg : (w * X ^ (N - r - k)).natDegree ≤ N - 1 := by
      refine natDegree_mul_le.trans ?_
      have := natDegree_X_pow_le (R := L) (N - r - k)
      omega
    have := hwy (N - r - k) hj
    rw [hy, momentFunctional_chartPoint x _ hdeg,
      show N - 1 = (r - 1) + (N - r) by omega, reflect_mul_X_pow (by omega) hj,
      mul_comp, X_pow_comp, show N - r - (N - r - k) = k by omega] at this
    exact this
  have hhann : AnnihilatesWindow x h (N - r) := by
    intro k hk
    have := momentFunctional_mul_add_C_pow x h (X + C (t : L)) (N - r) hhx (-(t : L)) k hk
    rwa [show X + C (t : L) + C (-(t : L)) = X by rw [C_neg]; ring] at this
  have hh0 := h2 h hhdeg hhann
  have hrw : reflect (r - 1) w = 0 := by
    have := congrArg (fun p => p.comp (X - C (t : L))) hh0
    simp only [hh, comp_assoc, zero_comp] at this
    rwa [add_C_comp_sub_C, comp_X] at this
  exact reflect_eq_zero_iff.mp hrw

/-! ## Vectors as polynomials, and maximal minors -/

/-- The polynomial `Σ v_i T^i` of a row vector. -/
def vecPoly {r : ℕ} (v : Fin r → L) : L[X] := ∑ i : Fin r, C (v i) * X ^ (i : ℕ)

theorem natDegree_vecPoly_le {r : ℕ} (v : Fin r → L) : (vecPoly v).natDegree ≤ r - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := i.isLt; omega)

theorem coeff_vecPoly {r : ℕ} (v : Fin r → L) (i : Fin r) : (vecPoly v).coeff i = v i := by
  classical
  rw [vecPoly, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro k _ hk
    rw [coeff_C_mul_X_pow, if_neg (fun h => hk (Fin.ext h.symm))]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem vecPoly_coeff {r : ℕ} {h : L[X]} (hdeg : h.natDegree < r) :
    vecPoly (fun i : Fin r => h.coeff i) = h := by
  rw [vecPoly, Fin.sum_univ_eq_sum_range (fun i => C (h.coeff i) * X ^ i)]
  conv_rhs => rw [h.as_sum_range' r hdeg]
  simp_rw [← C_mul_X_pow_eq_monomial]

theorem momentFunctional_vecPoly_mul_X_pow (x : Fin N → L) {r : ℕ} (v : Fin r → L) {j : ℕ}
    (hj : r + j ≤ N) :
    momentFunctional x (vecPoly v * X ^ j) =
      ∑ i : Fin r, v i * x ⟨i + j, by have := i.isLt; omega⟩ := by
  rw [vecPoly, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← pow_add, momentFunctional_C_mul_X_pow]

/-- **Vanishing maximal minors give a left-kernel polynomial.**  If every maximal minor of the
`(r+1)`-row Hankel matrix vanishes at `x`, some nonzero polynomial of degree `≤ r` annihilates the
window `0, …, N−1−r`. -/
theorem exists_annihilator_of_maximalMinors (x : Fin N → L) {r : ℕ} (hrN : 2 * r < N)
    (hmin : ∀ (c : Fin (r + 1) → ℕ) (hbound : ∀ j, (r + 1) + c j ≤ N), StrictMono c →
      Matrix.det (fun i j : Fin (r + 1) => x (RHTower.finiteHankelIndex c hbound i j)) = 0) :
    ∃ g : L[X], g ≠ 0 ∧ g.natDegree ≤ r ∧ AnnihilatesWindow x g (N - 1 - r) := by
  classical
  set v : Fin (r + 1) → Fin (N - r) → L := fun i c => x ⟨i + c, by omega⟩ with hv
  by_cases hli : LinearIndependent L v
  · exfalso
    obtain ⟨φ, hφ⟩ := exists_coordinateMinor_det_ne_zero_fin (r + 1) v hli
    have hinj : Function.Injective fun a => (φ a : ℕ) := by
      intro a b hab
      by_contra hne
      refine hφ (Matrix.det_zero_of_row_eq hne ?_)
      funext k
      simp only [coordinateMinor_apply, hv]
      congr 2
      simp only at hab
      rw [hab]
    set σ := Tuple.sort fun a => (φ a : ℕ)
    set c : Fin (r + 1) → ℕ := (fun a => (φ a : ℕ)) ∘ σ with hc
    have hcmono : StrictMono c :=
      (Tuple.monotone_sort _).strictMono_of_injective (hinj.comp σ.injective)
    have hbound : ∀ j, (r + 1) + c j ≤ N := fun j => by
      have := (φ (σ j)).isLt; simp only [hc, Function.comp]; omega
    have h0 := hmin c hbound hcmono
    have hmat : (fun i j : Fin (r + 1) => x (RHTower.finiteHankelIndex c hbound i j)) =
        (coordinateMinor v φ).transpose.submatrix id σ := by
      funext i j
      simp only [Matrix.submatrix_apply, Matrix.transpose_apply, coordinateMinor_apply, hv, id,
        RHTower.finiteHankelIndex, hc, Function.comp]
    rw [show Matrix.det (fun i j : Fin (r + 1) => x (RHTower.finiteHankelIndex c hbound i j)) =
        Matrix.det ((coordinateMinor v φ).transpose.submatrix id σ) by rw [← hmat],
      Matrix.det_permute', Matrix.det_transpose] at h0
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] at h0 <;>
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg,
        neg_mul, neg_eq_zero] at h0 <;> exact hφ h0
  · rw [Fintype.not_linearIndependent_iff] at hli
    obtain ⟨g, hg, i₀, hi₀⟩ := hli
    refine ⟨vecPoly g, fun h => hi₀ ?_, ?_, fun j hj => ?_⟩
    · rw [← coeff_vecPoly g i₀, h, coeff_zero]
    · exact (natDegree_vecPoly_le g).trans (by omega)
    · rw [momentFunctional_vecPoly_mul_X_pow x g (by omega)]
      have := congrFun hg ⟨j, by omega⟩
      simpa [Finset.sum_apply, hv] using this

/-- **A nonzero maximal minor kills every left-kernel polynomial.** -/
theorem eq_zero_of_annihilatesWindow_of_minor (x : Fin N → L) {r : ℕ} (c : Fin r → ℕ)
    (hbound : ∀ j, r + c j ≤ N)
    (hdet : Matrix.det (fun i j : Fin r => x (RHTower.finiteHankelIndex c hbound i j)) ≠ 0)
    {h : L[X]} (hdeg : h.natDegree < r) (hann : AnnihilatesWindow x h (N - r)) : h = 0 := by
  classical
  set v : Fin r → L := fun i => h.coeff i
  have hvec : Matrix.vecMul v (fun i j : Fin r => x (RHTower.finiteHankelIndex c hbound i j)) = 0 := by
    funext j
    have hj := hann (c j) (by have := hbound j; omega)
    rw [← vecPoly_coeff hdeg, momentFunctional_vecPoly_mul_X_pow x _ (hbound j)] at hj
    simpa [Matrix.vecMul, dotProduct, RHTower.finiteHankelIndex, v] using hj
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  rw [← vecPoly_coeff hdeg]
  have : (fun i : Fin r => h.coeff i) = 0 := hv0
  rw [this]
  simp [vecPoly]

/-- **An injective window gives a nonzero leading minor.** -/
theorem det_ne_zero_of_annihilatesWindow (y : Fin N → L) {r : ℕ} (hrN : 2 * r ≤ N)
    (hinj : ∀ w : L[X], w.natDegree < r → AnnihilatesWindow y w (r - 1) → w = 0) :
    Matrix.det (fun i j : Fin r => y ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩) ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; exact absurd (funext fun i => Fin.elim0 i) hv0
    · exact h
  have hw := hinj (vecPoly v) (by have := natDegree_vecPoly_le v; omega) (fun j hj => by
    rw [momentFunctional_vecPoly_mul_X_pow y v (by omega)]
    have := congrFun hv ⟨j, by omega⟩
    simpa [Matrix.vecMul, dotProduct] using this)
  exact hv0 (funext fun i => by rw [← coeff_vecPoly v i, hw, coeff_zero]; rfl)

/-- **The moved charts cover the rank-`r` locus.**  If every maximal `(r+1)`-minor vanishes at `x`
and some maximal `r`-minor does not, then for some `t ≤ r` the leading `r × r` Hankel minor of the
moved point is nonzero. -/
theorem exists_chartPoint_det_ne_zero [CharZero L] (x : Fin N → L) {r : ℕ} (hrN : 2 * r < N)
    (hmin : ∀ (c : Fin (r + 1) → ℕ) (hbound : ∀ j, (r + 1) + c j ≤ N), StrictMono c →
      Matrix.det (fun i j : Fin (r + 1) => x (RHTower.finiteHankelIndex c hbound i j)) = 0)
    (c : Fin r → ℕ) (hbound : ∀ j, r + c j ≤ N)
    (hdet : Matrix.det (fun i j : Fin r => x (RHTower.finiteHankelIndex c hbound i j)) ≠ 0) :
    ∃ t ∈ Finset.range (r + 1), Matrix.det (fun i j : Fin r =>
      chartPoint x (t : L) ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩) ≠ 0 := by
  obtain ⟨t, ht, hinj⟩ := exists_chartPoint_injective x hrN
    (exists_annihilator_of_maximalMinors x hrN hmin)
    (fun h hdeg hann => eq_zero_of_annihilatesWindow_of_minor x c hbound hdet hdeg hann)
  exact ⟨t, ht, det_ne_zero_of_annihilatesWindow _ hrN.le hinj⟩

end

end GaloisForLFunctions.HTGeometry
