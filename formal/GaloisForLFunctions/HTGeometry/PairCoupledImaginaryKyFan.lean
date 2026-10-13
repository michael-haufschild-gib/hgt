import GaloisForLFunctions.HTGeometry.SchurCharpoly

/-!
# Imaginary parts of eigenvalues under a pair-coupled anti-Hermitian part

Let `T` be a complex `N × N` matrix whose quadratic form has imaginary part

`Im ⟨x, T x⟩ = Σ_j 2 r_j · Im( conj(x_{p_j}) · x_{q_j} )`,

where `p, q : Fin m → Fin N` are injective with disjoint ranges and `r_j ≥ 0`.  (This holds for
`T = [[A, B], [−Bᴴ, D]]` with `A, D` Hermitian and `B` having the single entries `r_j` at
`(p_j, q_j)`.)  Then for every `σ ≥ 0` the eigenvalues `λ` of `T` (roots of the characteristic
polynomial, with multiplicity) satisfy

`Σ_λ (Im λ − σ)_+ ≤ Σ_j (r_j − σ)_+`
(`sum_roots_charpoly_im_sub_pos_le`).

Equivalently the positive imaginary parts are weakly submajorised by the `r_j`.

**Proof.**  Schur-triangulate `Uᴴ T U = R`.  The eigenvalues are the diagonal entries
`R_ii = ⟨U e_i, T U e_i⟩`, so `Im R_ii = Σ_j 2 r_j Im(conj U_{p_j i} U_{q_j i})`.  Put
`S = {i : Im R_ii > σ}` and `Z_j = Σ_{i∈S} conj(U_{p_j i}) U_{q_j i}`.  With
`a_j = Σ_{i∈S} |U_{p_j i}|²`, `b_j = Σ_{i∈S} |U_{q_j i}|²`, Cauchy–Schwarz on `S` and on its
complement (rows of `U` are orthonormal) gives `|Z_j|² ≤ a_j b_j` and
`|Z_j|² ≤ (1 − a_j)(1 − b_j)`, hence `w_j := 2|Z_j| ≤ 1` and `w_j ≤ a_j + b_j`; since the columns
of `U` are unit vectors, `Σ_j (a_j + b_j) ≤ |S|`.  Therefore
`Σ_{i∈S} (Im R_ii − σ) ≤ Σ_j r_j w_j − |S| σ ≤ Σ_j w_j (r_j − σ) ≤ Σ_j (r_j − σ)_+`.
-/

open Matrix Finset Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cauchy–Schwarz for a finite complex sum, in squared-norm form. -/
theorem norm_sum_conj_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, (starRingEnd ℂ) (a i) * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (starRingEnd ℂ) (a i) * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)
  have h0 : 0 ≤ ‖∑ i ∈ s, (starRingEnd ℂ) (a i) * b i‖ := norm_nonneg _
  nlinarith

/-- A weight in `[0,1]` times a real number is at most its positive part. -/
theorem mul_le_max_sub_zero {w x : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : w * x ≤ max x 0 := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]; nlinarith
  · rw [max_eq_right hx]; nlinarith

/-- **Pair-coupled Ky Fan bound.** -/
theorem sum_roots_charpoly_im_sub_pos_le {N m : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin m → Fin N) (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : ∀ j k, p j ≠ q k) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hT : ∀ x : Fin N → ℂ, (star x ⬝ᵥ T *ᵥ x).im =
      ∑ j, 2 * r j * ((starRingEnd ℂ) (x (p j)) * x (q j)).im)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (T.charpoly.roots.map fun z => max (z.im - σ) 0).sum ≤ ∑ j, max (r j - σ) 0 := by
  classical
  obtain ⟨U, R, hU1, hU2, hR, hUT⟩ := exists_schur_triangulation N T
  -- the eigenvalues are the Schur diagonal
  have hroots : T.charpoly.roots = Finset.univ.val.map fun i => R i i := by
    have hprod : T.charpoly
        = ((Finset.univ.val.map fun i : Fin N => R i i).map fun a : ℂ => X - C a).prod := by
      rw [charpoly_of_schur hU1 hU2 hR hUT, Finset.prod, Multiset.map_map]
      rfl
    rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  have hsum : (T.charpoly.roots.map fun z => max (z.im - σ) 0).sum =
      ∑ i, max ((R i i).im - σ) 0 := by
    rw [hroots, Multiset.map_map]; rfl
  rw [hsum]
  -- columns of `U`
  set col : Fin N → Fin N → ℂ := fun i u => U u i with hcol
  have hdiag : ∀ i, R i i = star (col i) ⬝ᵥ T *ᵥ col i := by
    intro i
    rw [← hUT]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec, hcol, Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  -- row and column orthonormality
  have hrow : ∀ u v, ∑ i, U u i * (starRingEnd ℂ) (U v i) = if u = v then 1 else 0 := by
    intro u v
    have := congrArg (fun A => A u v) hU2
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  have hcolnorm : ∀ i, ∑ u, ‖U u i‖ ^ 2 = 1 := by
    intro i
    have := congrArg (fun A => A i i) hU1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      RCLike.star_def] at this
    have h' : ((∑ u, ‖U u i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Complex.conj_mul']
    exact_mod_cast h'
  have hrownorm : ∀ u, ∑ i, ‖U u i‖ ^ 2 = 1 := by
    intro u
    have := hrow u u
    simp only [if_true] at this
    have h' : ((∑ i, ‖U u i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.mul_conj']
    exact_mod_cast h'
  set S := Finset.univ.filter fun i => σ < (R i i).im with hS
  have hpos : ∑ i, max ((R i i).im - σ) 0 = ∑ i ∈ S, ((R i i).im - σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · exact max_eq_left (by linarith)
    · exact max_eq_right (by linarith [not_lt.mp h])
  rw [hpos]
  -- the overlap amplitudes
  set Z : Fin m → ℂ := fun j => ∑ i ∈ S, (starRingEnd ℂ) (U (p j) i) * U (q j) i with hZ
  set a : Fin m → ℝ := fun j => ∑ i ∈ S, ‖U (p j) i‖ ^ 2 with ha
  set b : Fin m → ℝ := fun j => ∑ i ∈ S, ‖U (q j) i‖ ^ 2 with hb
  have hIm : ∑ i ∈ S, (R i i).im = ∑ j, 2 * r j * (Z j).im := by
    simp only [hdiag, hT, hZ, hcol]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, Complex.im_sum]
  have hcompl : ∀ u : Fin N, ∑ i ∈ Sᶜ, ‖U u i‖ ^ 2 = 1 - ∑ i ∈ S, ‖U u i‖ ^ 2 := by
    intro u
    rw [← hrownorm u, ← Finset.sum_add_sum_compl S]; ring
  have ha1 : ∀ j, a j ≤ 1 := by
    intro j
    have := hcompl (p j)
    have h0 : 0 ≤ ∑ i ∈ Sᶜ, ‖U (p j) i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    simp only [ha]; linarith
  have hb1 : ∀ j, b j ≤ 1 := by
    intro j
    have := hcompl (q j)
    have h0 : 0 ≤ ∑ i ∈ Sᶜ, ‖U (q j) i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    simp only [hb]; linarith
  have ha0 : ∀ j, 0 ≤ a j := fun j => Finset.sum_nonneg fun _ _ => by positivity
  have hb0 : ∀ j, 0 ≤ b j := fun j => Finset.sum_nonneg fun _ _ => by positivity
  have hZin : ∀ j, ‖Z j‖ ^ 2 ≤ a j * b j := fun j => norm_sum_conj_mul_sq_le S _ _
  have hZout : ∀ j, ‖Z j‖ ^ 2 ≤ (1 - a j) * (1 - b j) := by
    intro j
    have hzero : ∑ i, (starRingEnd ℂ) (U (p j) i) * U (q j) i = 0 := by
      have := hrow (q j) (p j)
      rw [if_neg (hpq j j).symm] at this
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hZc : Z j = -∑ i ∈ Sᶜ, (starRingEnd ℂ) (U (p j) i) * U (q j) i := by
      rw [← Finset.sum_add_sum_compl S] at hzero
      simp only [hZ]
      linear_combination hzero
    have := norm_sum_conj_mul_sq_le Sᶜ (fun i => U (p j) i) (fun i => U (q j) i)
    rw [hZc, norm_neg]
    rw [hcompl (p j), hcompl (q j)] at this
    exact this
  -- weights
  have hw1 : ∀ j, 2 * ‖Z j‖ ≤ 1 := by
    intro j
    have h1 := hZin j; have h2 := hZout j
    have ha' := ha0 j; have ha'' := ha1 j; have hb' := hb0 j; have hb'' := hb1 j
    have hprod : (‖Z j‖ ^ 2) ^ 2 ≤ (a j * (1 - a j)) * (b j * (1 - b j)) := by
      have := mul_le_mul h1 h2 (by positivity) (by nlinarith)
      nlinarith
    have hqa : a j * (1 - a j) ≤ 1 / 4 := by nlinarith [sq_nonneg (a j - 1 / 2)]
    have hqb : b j * (1 - b j) ≤ 1 / 4 := by nlinarith [sq_nonneg (b j - 1 / 2)]
    have h4 : (‖Z j‖ ^ 2) ^ 2 ≤ 1 / 16 := by
      have : (a j * (1 - a j)) * (b j * (1 - b j)) ≤ 1 / 4 * (1 / 4) :=
        mul_le_mul hqa hqb (by nlinarith) (by norm_num)
      linarith
    have hn := norm_nonneg (Z j)
    nlinarith [sq_nonneg (‖Z j‖ - 1 / 2), sq_nonneg (‖Z j‖ + 1 / 2)]
  have hwab : ∀ j, 2 * ‖Z j‖ ≤ a j + b j := by
    intro j
    have h1 := hZin j
    have hn := norm_nonneg (Z j)
    nlinarith [sq_nonneg (a j - b j), ha0 j, hb0 j]
  have hwS : ∑ j, 2 * ‖Z j‖ ≤ (S.card : ℝ) := by
    calc ∑ j, 2 * ‖Z j‖ ≤ ∑ j, (a j + b j) := Finset.sum_le_sum fun j _ => hwab j
      _ = ∑ i ∈ S, (∑ j, ‖U (p j) i‖ ^ 2 + ∑ j, ‖U (q j) i‖ ^ 2) := by
          simp only [ha, hb, Finset.sum_add_distrib]
          rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := S)]
      _ ≤ ∑ i ∈ S, ∑ u, ‖U u i‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hdisj : Disjoint (Finset.univ.map ⟨p, hp⟩) (Finset.univ.map ⟨q, hq⟩) := by
            rw [Finset.disjoint_left]
            intro u hu hu'
            obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hu
            obtain ⟨k, -, hk⟩ := Finset.mem_map.mp hu'
            exact hpq j k hk.symm
          have h1 : ∑ j, ‖U (p j) i‖ ^ 2 + ∑ j, ‖U (q j) i‖ ^ 2 =
              ∑ u ∈ Finset.univ.map ⟨p, hp⟩ ∪ Finset.univ.map ⟨q, hq⟩, ‖U u i‖ ^ 2 := by
            rw [Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
            rfl
          rw [h1]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => by positivity
      _ = (S.card : ℝ) := by simp [hcolnorm]
  -- assemble
  have hmain : ∑ i ∈ S, ((R i i).im - σ) ≤ ∑ j, (2 * ‖Z j‖) * (r j - σ) := by
    rw [Finset.sum_sub_distrib, hIm, Finset.sum_const, nsmul_eq_mul]
    have hterm : ∀ j, 2 * r j * (Z j).im ≤ (2 * ‖Z j‖) * r j := by
      intro j
      have := Complex.im_le_norm (Z j)
      nlinarith [hr j]
    have h1 : ∑ j, 2 * r j * (Z j).im ≤ ∑ j, (2 * ‖Z j‖) * r j := Finset.sum_le_sum fun j _ => hterm j
    have h2 : ∑ j, (2 * ‖Z j‖) * (r j - σ) = ∑ j, (2 * ‖Z j‖) * r j - (∑ j, 2 * ‖Z j‖) * σ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    nlinarith
  calc ∑ i ∈ S, ((R i i).im - σ) ≤ ∑ j, (2 * ‖Z j‖) * (r j - σ) := hmain
    _ ≤ ∑ j, max (r j - σ) 0 :=
        Finset.sum_le_sum fun j _ => mul_le_max_sub_zero (by positivity) (hw1 j)

end

end GaloisForLFunctions.HTGeometry
