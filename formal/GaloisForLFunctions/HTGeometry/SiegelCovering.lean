import GaloisForLFunctions.HTGeometry.SiegelOrbitMoves

/-!
# Every positive definite form is unimodularly equivalent to a Siegel form

Lattice basis reduction, assembled.  The potential is bounded below along the orbit, because the
comparison form `γᵀγ` of a congruate is integral and the ellipticity constant of `A` transfers to it
unchanged; and every state that is not already reduced admits a move contracting the potential by
`3/4`.  The descent scheme then produces a reduced state.

* `exists_ellipticity` : a positive definite form dominates a multiple of the identity.
* `potentialOf_ge_of_inOrbit` : **the potential is bounded below along the orbit.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

theorem dotProduct_self_le (n : ℕ) (v : Fin n → ℝ) : v ⬝ᵥ v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  classical
  have hterm : ∀ i : Fin n, v i * v i ≤ ‖v‖ ^ 2 := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa using this
    nlinarith [abs_nonneg (v i), sq_abs (v i), norm_nonneg v]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **A positive definite form dominates a multiple of the identity.** -/
theorem exists_ellipticity {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  classical
  have hsymm : A ∈ symmMatrices n := by
    show Aᵀ = A
    have h : Aᴴ = A := hA.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set P : posDefCone n := ⟨⟨A, hsymm⟩, hA⟩ with hP
  obtain ⟨m, hm, hlow⟩ := exists_lower_bound_of_isCompact (K := {P}) isCompact_singleton hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨m / (n : ℝ), div_pos hm hnR, fun v => ?_⟩
  have hq : m * ‖v‖ ^ 2 ≤ quadForm P v := quadForm_ge_of_sphere_bound (hlow P rfl) v
  have hqv : quadForm P v = v ⬝ᵥ (A *ᵥ v) := rfl
  have hbound := dotProduct_self_le n v
  rw [hqv] at hq
  have hstep : m / (n : ℝ) * (v ⬝ᵥ v) ≤ m / (n : ℝ) * ((n : ℝ) * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt (div_pos hm hnR))
  have hsimp : m / (n : ℝ) * ((n : ℝ) * ‖v‖ ^ 2) = m * ‖v‖ ^ 2 := by
    field_simp
  rw [hsimp] at hstep
  exact le_trans hstep hq

/-- An integral unimodular matrix has invertible determinant. -/
theorem IsIntUnimodular.isUnit_det {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : IsIntUnimodular γ) :
    IsUnit γ.det := by
  obtain ⟨g, hgu, hg⟩ := hγ
  have hmap : γ = g.map (fun z : ℤ => (z : ℝ)) := by
    ext a b
    exact hg a b
  have hdc : (g.map (fun z : ℤ => (z : ℝ))).det = ((g.det : ℤ) : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) g).symm
  rw [hmap, hdc]
  refine (isUnit_iff_ne_zero).2 ?_
  intro hcon
  have hgz : g.det = 0 := by exact_mod_cast hcon
  exact ((Matrix.isUnit_iff_isUnit_det g).1 hgu).ne_zero hgz

/-- **The potential is bounded below along the orbit.** -/
theorem potentialOf_ge_of_inOrbit {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (J : JacobiData n) (hJ : InOrbit A J.form) :
    (∏ k : Fin (n + 1), lam ^ (k : ℕ)) ≤ potentialOf J.form := by
  classical
  obtain ⟨γ, hγ, hform⟩ := hJ
  obtain ⟨g, hgu, hg⟩ := id hγ
  have hdet : IsUnit γ.det := hγ.isUnit_det
  have hinj : Function.Injective γ.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det γ).2 hdet)
  have hBpos : (γᵀ * (1 : Matrix (Fin n) (Fin n) ℝ) * γ).PosDef := by
    have hcast : γᴴ * (1 : Matrix (Fin n) (Fin n) ℝ) * γ
        = γᵀ * (1 : Matrix (Fin n) (Fin n) ℝ) * γ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hcast]
    exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
  obtain ⟨K, hK⟩ := exists_jacobiData hBpos
  -- the comparison form is integral
  have hKB : ∀ a b : Fin n, K.form a b = (((gᵀ * g) a b : ℤ) : ℝ) := by
    intro a b
    rw [hK]
    show (γᵀ * (1 : Matrix (Fin n) (Fin n) ℝ) * γ) a b = _
    rw [Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by
      rw [Matrix.transpose_apply, Matrix.transpose_apply, hg m a, hg m b]
  -- domination
  have hdom : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v) := by
    intro v
    have hKv : v ⬝ᵥ (K.form *ᵥ v) = (γ *ᵥ v) ⬝ᵥ (γ *ᵥ v) := by
      rw [hK, quadForm_congr, Matrix.one_mulVec]
    have hJv : v ⬝ᵥ (J.form *ᵥ v) = (γ *ᵥ v) ⬝ᵥ (A *ᵥ (γ *ᵥ v)) := by
      rw [hform, quadForm_congr]
    rw [hKv, hJv]
    exact hell (γ *ᵥ v)
  refine Finset.prod_le_prod (fun k _ => pow_nonneg hlam.le _) fun k _ => ?_
  exact pow_le_det_leadingBlock hlam.le hdom hKB (Fin.is_le k)

/-- **Every positive definite form is unimodularly equivalent to one satisfying the Siegel
bounds.**  This is the covering statement of reduction theory: the `SL(n, ℤ)`-translates of a Siegel
set exhaust the cone of positive definite forms. -/
theorem exists_siegel_inOrbit {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ J : JacobiData n, InOrbit A J.form ∧ J.IsSiegel 2 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    obtain ⟨J, hJ⟩ := exists_jacobiData hA
    exact ⟨J, by rw [hJ]; exact inOrbit_refl A,
      ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  · obtain ⟨lam, hlam, hell⟩ := exists_ellipticity hA hn
    obtain ⟨J₀, hJ₀⟩ := exists_jacobiData hA
    have hJ₀orb : InOrbit A J₀.form := by rw [hJ₀]; exact inOrbit_refl A
    by_contra hcon
    have hres : ∃ _ : {J : JacobiData n // InOrbit A J.form},
        ∃ J : JacobiData n, InOrbit A J.form ∧ J.IsSiegel 2 1 := by
      refine exists_terminal_of_contracting
        (fun s : {J : JacobiData n // InOrbit A J.form} => potentialOf s.1.form)
        (fun _ => ∃ J : JacobiData n, InOrbit A J.form ∧ J.IsSiegel 2 1)
        (c := ∏ k : Fin (n + 1), lam ^ (k : ℕ)) (q := 3 / 4)
        (Finset.prod_pos fun k _ => pow_pos hlam _) (by norm_num) (by norm_num)
        (fun s => potentialOf_ge_of_inOrbit hlam hell s.1 s.2) ?_ ⟨J₀, hJ₀orb⟩
      intro s hs
      obtain ⟨J', hJ'orb, hJ'pot, hJ'red⟩ := exists_sizeReduced_inOrbit s.1 s.2
      have hnotS : ¬ J'.IsSiegel 2 1 := fun h => hs ⟨J', hJ'orb, h⟩
      have hnotterm : ¬ (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
          3 / 4 * J'.d i ≤ J'.projNorm i (Pi.single j (1 : ℝ))) :=
        fun h => hnotS (isSiegel_two_of_terminal J' hJ'red h)
      push Not at hnotterm
      obtain ⟨i, j, hjs, hfail⟩ := hnotterm
      have hij : i ≠ j := by
        intro hc
        rw [hc] at hjs
        omega
      have hji : i ≤ j := Fin.le_def.2 (by omega)
      obtain ⟨J'', hJ''orb, hJ''lt⟩ := exists_swap_inOrbit J' hJ'orb hij hji hjs hfail
      exact ⟨⟨J'', hJ''orb⟩, by
        show potentialOf J''.form ≤ 3 / 4 * potentialOf s.1.form
        rw [← hJ'pot]
        exact le_of_lt hJ''lt⟩
    obtain ⟨_, hPP⟩ := hres
    exact hcon hPP

end GaloisForLFunctions.HTGeometry
