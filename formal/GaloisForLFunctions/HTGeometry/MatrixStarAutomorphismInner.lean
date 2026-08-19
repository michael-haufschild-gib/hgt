import GaloisForLFunctions.HTGeometry.UnitalCPInverseRigidity

/-!
# A unital star automorphism of a matrix algebra is inner

Every injective unital star algebra endomorphism of `Matrix n n ℂ` is conjugation by a unitary.
The proof is the classical matrix-unit construction: the images `F i j = Θ(E i j)` form a system
of matrix units, a nonzero vector in the range of `F i₀ i₀` generates an orthogonal family
`u i = F i i₀ v`, and the matrix with those columns intertwines `Θ` with the identity.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Moving a matrix across the pairing turns it into its adjoint. -/
theorem star_mulVec_dotProduct (M : Matrix n n ℂ) (x y : n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Mᴴ *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring

theorem eq_zero_of_mulVec_eq_zero {M : Matrix n n ℂ} (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- The identity matrix is the sum of the diagonal matrix units. -/
theorem one_eq_sum_diagonal_single :
    (1 : Matrix n n ℂ) = ∑ i, Matrix.single i i (1 : ℂ) := by
  ext p q
  rw [Matrix.sum_apply]
  by_cases h : p = q
  · subst h
    rw [Matrix.one_apply_eq, Finset.sum_eq_single p]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · intro hc
      exact absurd (Finset.mem_univ p) hc
  · rw [Matrix.one_apply_ne h, Finset.sum_eq_zero]
    intro b _
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

/-- **A unital injective star endomorphism of a matrix algebra is a unitary conjugation.** -/
theorem exists_unitary_conjugation_of_starAlgHom
    {Θ : Matrix n n ℂ → Matrix n n ℂ}
    (hadd : ∀ X Y, Θ (X + Y) = Θ X + Θ Y)
    (hsmul : ∀ (c : ℂ) (X), Θ (c • X) = c • Θ X)
    (hmul : ∀ X Y, Θ (X * Y) = Θ X * Θ Y)
    (hstar : ∀ X, Θ Xᴴ = (Θ X)ᴴ)
    (hone : Θ 1 = 1) (hinj : Function.Injective Θ) :
    ∃ U : Matrix n n ℂ, U ∈ unitary (Matrix n n ℂ) ∧ ∀ X, Θ X = U * X * star U := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, ⟨by simp, by simp⟩, fun X => Subsingleton.elim _ _⟩
  obtain ⟨i₀⟩ := hn
  have hzero : Θ 0 = 0 := by simpa using hsmul 0 0
  have hfsum : ∀ (s : Finset n) (f : n → Matrix n n ℂ),
      Θ (∑ i ∈ s, f i) = ∑ i ∈ s, Θ (f i) := by
    intro s f
    induction s using Finset.induction with
    | empty => simpa using hzero
    | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]
  -- the image system of matrix units
  set F : n → n → Matrix n n ℂ := fun i j => Θ (Matrix.single i j (1 : ℂ)) with hFdef
  have hFmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    rw [hFdef]
    dsimp only
    rw [← hmul]
    by_cases h : j = k
    · subst h
      rw [if_pos rfl, Matrix.single_mul_single_same]
      simp
    · have hprod : Matrix.single i j (1 : ℂ) * Matrix.single k l (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i j k h (1 : ℂ)
      rw [if_neg h, hprod, hzero]
  have hFstar : ∀ i j, (F i j)ᴴ = F j i := by
    intro i j
    rw [hFdef]
    dsimp only
    rw [← hstar, Matrix.conjTranspose_single]
    simp
  have hFsum : ∑ i, F i i = 1 := by
    rw [hFdef]
    dsimp only
    rw [← hfsum, ← one_eq_sum_diagonal_single, hone]
  -- a nonzero vector in the range of the first diagonal unit
  have hFne : F i₀ i₀ ≠ 0 := by
    intro hcon
    have hz : Θ (Matrix.single i₀ i₀ (1 : ℂ)) = Θ 0 := by
      rw [hzero]; exact hcon
    have : Matrix.single i₀ i₀ (1 : ℂ) = 0 := hinj hz
    have h1 : (Matrix.single i₀ i₀ (1 : ℂ)) i₀ i₀ = 1 := by simp
    rw [this] at h1
    simp at h1
  obtain ⟨v, hv⟩ : ∃ v : n → ℂ, F i₀ i₀ *ᵥ v ≠ 0 := by
    by_contra hcon
    refine hFne (eq_zero_of_mulVec_eq_zero fun x => ?_)
    by_contra hx
    exact hcon ⟨x, hx⟩
  set w : n → ℂ := F i₀ i₀ *ᵥ v with hwdef
  have hwidem : F i₀ i₀ *ᵥ w = w := by
    rw [hwdef, Matrix.mulVec_mulVec, hFmul i₀ i₀ i₀ i₀, if_pos rfl]
  set u : n → n → ℂ := fun i => F i i₀ *ᵥ w with hudef
  have hui₀ : u i₀ = w := by rw [hudef]; exact hwidem
  set sr : ℝ := ∑ p, Complex.normSq (w p) with hsrdef
  have hsr : star w ⬝ᵥ w = (sr : ℂ) := by
    rw [hsrdef, dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by
      simp [Complex.normSq_eq_conj_mul_self]
  have hsrpos : 0 < sr := by
    rcases Function.ne_iff.mp hv with ⟨p, hp⟩
    refine Finset.sum_pos' (fun q _ => Complex.normSq_nonneg _) ⟨p, Finset.mem_univ p, ?_⟩
    exact Complex.normSq_pos.mpr (by simpa [hwdef] using hp)
  have horth : ∀ i j, star (u i) ⬝ᵥ (u j) = if i = j then (sr : ℂ) else 0 := by
    intro i j
    rw [hudef]
    dsimp only
    rw [star_mulVec_dotProduct, hFstar, Matrix.mulVec_mulVec, hFmul i₀ i j i₀]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, hwidem, hsr]
    · rw [if_neg h, if_neg h]
      simp
  set U₀ : Matrix n n ℂ := Matrix.of (fun p q => u q p) with hU₀def
  have hU₀gram : U₀ᴴ * U₀ = (sr : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    rw [Matrix.mul_apply]
    have : ∑ p, U₀ᴴ i p * U₀ p j = star (u i) ⬝ᵥ (u j) := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun p _ => by
        simp [hU₀def, Matrix.conjTranspose_apply, RCLike.star_def]
    rw [this, horth]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Matrix.one_apply_ne h]
  have hFmulVec : ∀ i j q, F i j *ᵥ u q = if j = q then u i else 0 := by
    intro i j q
    rw [hudef]
    dsimp only
    rw [Matrix.mulVec_mulVec, hFmul i j q i₀]
    by_cases h : j = q
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg h]
      simp
  have hkey : ∀ i j, F i j * U₀ = U₀ * Matrix.single i j (1 : ℂ) := by
    intro i j
    ext p q
    have hl : (F i j * U₀) p q = (F i j *ᵥ u q) p := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun r _ => by simp [hU₀def]
    have hr : (U₀ * Matrix.single i j (1 : ℂ)) p q = if j = q then u i p else 0 := by
      rw [Matrix.mul_apply]
      by_cases h : j = q
      · subst h
        rw [if_pos rfl, Finset.sum_eq_single i]
        · simp [hU₀def]
        · intro b _ hb
          simp [Ne.symm hb]
        · intro hcon; exact absurd (Finset.mem_univ i) hcon
      · rw [if_neg h, Finset.sum_eq_zero]
        intro b _
        simp [h]
    rw [hl, hr, hFmulVec]
    by_cases h : j = q
    · subst h; simp
    · simp [h]
  have hlin : ∀ X : Matrix n n ℂ, Θ X * U₀ = U₀ * X := by
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    rw [hfsum]
    have hinner : ∀ i, Θ (∑ j, Matrix.single i j (X i j)) = ∑ j, (X i j) • F i j := by
      intro i
      rw [hfsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by
        rw [Matrix.smul_single]; simp, hsmul]
    simp only [hinner]
    rw [Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, hkey i j, show Matrix.single i j (X i j)
      = (X i j) • Matrix.single i j (1 : ℂ) by rw [Matrix.smul_single]; simp,
      Matrix.mul_smul]
  -- normalise
  set t : ℝ := (Real.sqrt sr)⁻¹ with htdef
  have htsq : (t : ℂ) * (t : ℂ) * (sr : ℂ) = 1 := by
    have hs : Real.sqrt sr * Real.sqrt sr = sr := Real.mul_self_sqrt (le_of_lt hsrpos)
    have hne : Real.sqrt sr ≠ 0 := by
      simpa using Real.sqrt_ne_zero'.mpr hsrpos
    have htt : t * t = sr⁻¹ := by
      rw [htdef, ← mul_inv, hs]
    have hmain : t * t * sr = 1 := by
      rw [htt, inv_mul_cancel₀ (ne_of_gt hsrpos)]
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hmain
  refine ⟨(t : ℂ) • U₀, ?_, ?_⟩
  · have hgram : star ((t : ℂ) • U₀) * ((t : ℂ) • U₀) = 1 := by
      rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hst : star (t : ℂ) = (t : ℂ) := by simp
      rw [hst, show (star U₀ : Matrix n n ℂ) = U₀ᴴ from rfl, hU₀gram, smul_smul,
        show (t : ℂ) * (t : ℂ) * (sr : ℂ) = 1 from htsq, one_smul]
    exact ⟨hgram, mul_eq_one_comm.mpr hgram⟩
  · intro X
    have hU : star ((t : ℂ) • U₀) * ((t : ℂ) • U₀) = 1 := by
      rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hst : star (t : ℂ) = (t : ℂ) := by simp
      rw [hst, show (star U₀ : Matrix n n ℂ) = U₀ᴴ from rfl, hU₀gram, smul_smul,
        show (t : ℂ) * (t : ℂ) * (sr : ℂ) = 1 from htsq, one_smul]
    have hU' : ((t : ℂ) • U₀) * star ((t : ℂ) • U₀) = 1 := mul_eq_one_comm.mpr hU
    have hstep : Θ X * ((t : ℂ) • U₀) = ((t : ℂ) • U₀) * X := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hlin]
    calc Θ X = Θ X * (((t : ℂ) • U₀) * star ((t : ℂ) • U₀)) := by rw [hU', Matrix.mul_one]
      _ = (Θ X * ((t : ℂ) • U₀)) * star ((t : ℂ) • U₀) := by rw [Matrix.mul_assoc]
      _ = ((t : ℂ) • U₀) * X * star ((t : ℂ) • U₀) := by rw [hstep]

end

end GaloisForLFunctions.HTGeometry
