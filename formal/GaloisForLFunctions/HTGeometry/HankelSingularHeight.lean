import GaloisForLFunctions.HTGeometry.HankelChartCover

/-!
# The singular locus of a Hankel secant variety has codimension at least two

Let `A = K[x]/I_{s+1}` and `J ⊆ A` the image of `I_s`, the ideal of the maximal `(s+1)`-minors.
Every prime `P ⊇ J` has height at least two: it contains the prime

`Q = ker (x_n ↦ Σ_{j<s} U_j T_j^n + U_s · 0^n)`

of "`s` atoms plus an atom at the origin", and `0 ⊊ Q ⊊ P`.

* `Q ⊆ I_s`: killing the weight of the origin atom turns the map into the `s`-atom map;
* `Q ⊇ I_{s+1}`, so `Q` is a prime of `A`;
* the shifted leading minor `det (x_{i+j+1})` lies in `Q` (the origin atom has no moments of
  positive order, so it is an `s`-atom minor) but not in `I_{s+1}`;
* the leading minor `det (x_{i+j})` lies in `I_s` but not in `Q`: at `s` atoms with nodes
  `1, …, s` and one at `0` it is the square of a nonzero Vandermonde determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type) [Field K]

/-- Killing the node of the last atom: `T_s ↦ 0`. -/
def lastNodeZero (s : ℕ) :
    MvPolynomial (Fin (s + 1) × Fin 2) K →ₐ[K] MvPolynomial (Fin (s + 1) × Fin 2) K :=
  aeval fun a => if a = (Fin.last s, 1) then 0 else X a

/-- Killing the weight of the last atom: `U_s ↦ 0`. -/
def lastWeightZero (s : ℕ) :
    MvPolynomial (Fin (s + 1) × Fin 2) K →ₐ[K] MvPolynomial (Fin (s + 1) × Fin 2) K :=
  aeval fun a => if a = (Fin.last s, 0) then 0 else X a

/-- `s` atoms plus an atom at the origin. -/
def originParam (N s : ℕ) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin (s + 1) × Fin 2) K :=
  (lastNodeZero K s : MvPolynomial (Fin (s + 1) × Fin 2) K →+* _).comp
    (RHTower.finiteHankelSecantParameterization K N (s + 1))

/-- The embedding of the `s`-atom coordinates. -/
def atomEmbed (s : ℕ) : MvPolynomial (Fin s × Fin 2) K →ₐ[K] MvPolynomial (Fin (s + 1) × Fin 2) K :=
  rename (Prod.map Fin.castSucc id)

theorem atomEmbed_injective (s : ℕ) : Function.Injective (atomEmbed K s) :=
  rename_injective _ fun a b h =>
    Prod.ext (Fin.castSucc_injective s (congrArg Prod.fst h)) (by simpa using congrArg Prod.snd h)

theorem originParam_X (N s : ℕ) (n : Fin N) :
    originParam K N s (X n) = ∑ j : Fin (s + 1), X (j, (0 : Fin 2)) *
      (if j = Fin.last s then 0 else X (j, (1 : Fin 2))) ^ (n : ℕ) := by
  simp only [originParam, RingHom.comp_apply, RHTower.finiteHankelSecantParameterization_X,
    RHTower.deningerHankelSecantMoment, RingHom.coe_coe, map_sum, map_mul, map_pow, lastNodeZero,
    aeval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_neg (by simp)]
  congr 2
  by_cases hj : j = Fin.last s
  · rw [if_pos (by rw [hj]), if_pos hj]
  · rw [if_neg (by simp [hj]), if_neg hj]

theorem lastWeightZero_comp_originParam (N s : ℕ) :
    (lastWeightZero K s).toRingHom.comp (originParam K N s) =
      (atomEmbed K s).toRingHom.comp (RHTower.finiteHankelSecantParameterization K N s) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) fun n => ?_
  · simp [originParam, RHTower.finiteHankelSecantParameterization,
      RHTower.deningerHankelSecantParameterization, lastNodeZero, lastWeightZero, atomEmbed]
  · rw [RingHom.comp_apply, originParam_X, RingHom.comp_apply,
      RHTower.finiteHankelSecantParameterization_X, RHTower.deningerHankelSecantMoment,
      AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe, map_sum,
      map_sum, Fin.sum_univ_castSucc]
    have hlast : lastWeightZero K s (X (Fin.last s, (0 : Fin 2))) = 0 := by
      rw [lastWeightZero, aeval_X, if_pos rfl]
    rw [map_mul, hlast, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : Fin.castSucc j ≠ Fin.last s := Fin.castSucc_ne_last j
    simp only [map_mul, map_pow, lastWeightZero, atomEmbed, aeval_X, rename_X,
      Prod.map_apply, id, Prod.mk.injEq, hj, false_and, if_false]

/-- The prime of `s` atoms plus an atom at the origin. -/
def originIdeal (N s : ℕ) : Ideal (MvPolynomial (Fin N) K) := RingHom.ker (originParam K N s)

instance originIdeal_isPrime (N s : ℕ) : (originIdeal K N s).IsPrime := RingHom.ker_isPrime _

theorem secantIdeal_le_originIdeal (N s : ℕ) :
    RHTower.finiteHankelSecantIdeal K N (s + 1) ≤ originIdeal K N s := by
  intro p hp
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker] at hp
  rw [originIdeal, RingHom.mem_ker, originParam, RingHom.comp_apply, hp, map_zero]

theorem originIdeal_le_secantIdeal (N s : ℕ) :
    originIdeal K N s ≤ RHTower.finiteHankelSecantIdeal K N s := by
  intro p hp
  rw [originIdeal, RingHom.mem_ker] at hp
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker]
  apply atomEmbed_injective K s
  have := congrArg (fun f => f p) (lastWeightZero_comp_originParam K N s)
  simp only [RingHom.comp_apply, hp, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [map_zero]
  exact this.symm

/-- The atomic Hankel determinant: `det (Σ_k w_k τ_k^{a+b}) = det(V_τ)² ∏ w_k`. -/
theorem det_atomicHankel {m : ℕ} (τ w : Fin m → K) :
    Matrix.det (fun a b : Fin m => ∑ k, w k * τ k ^ ((a : ℕ) + b)) =
      (Matrix.vandermonde τ).det ^ 2 * ∏ k, w k := by
  have h : (fun a b : Fin m => ∑ k, w k * τ k ^ ((a : ℕ) + b)) =
      (Matrix.vandermonde τ).transpose * Matrix.diagonal w * Matrix.vandermonde τ := by
    funext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      pow_add]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem det_atomicHankel_ne_zero [CharZero K] {m : ℕ} {τ w : Fin m → K}
    (hτ : Function.Injective τ) (hw : ∀ k, w k ≠ 0) :
    Matrix.det (fun a b : Fin m => ∑ k, w k * τ k ^ ((a : ℕ) + b)) ≠ 0 := by
  rw [det_atomicHankel]
  exact mul_ne_zero (pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hτ))
    (Finset.prod_ne_zero_iff.mpr fun k _ => hw k)

/-- The leading maximal `(s+1)`-minor `det (x_{i+j})`. -/
def leadSecantMinor (N s : ℕ) (hsN : 2 * (s + 1) ≤ N) : MvPolynomial (Fin N) K :=
  RHTower.finiteHankelMaximalMinorOver K (fun j : Fin (s + 1) => (j : ℕ))
    (fun j => by have := j.isLt; omega)

/-- The shifted maximal `(s+1)`-minor `det (x_{i+j+1})`. -/
def shiftSecantMinor (N s : ℕ) (hsN : 2 * (s + 1) < N) : MvPolynomial (Fin N) K :=
  RHTower.finiteHankelMaximalMinorOver K (fun j : Fin (s + 1) => (j : ℕ) + 1)
    (fun j => by have := j.isLt; omega)

theorem leadSecantMinor_mem (N s : ℕ) (hsN : 2 * (s + 1) ≤ N) :
    leadSecantMinor K N s hsN ∈ RHTower.finiteHankelSecantIdeal K N s :=
  Ideal.subset_span ⟨_, _, fun _ _ h => h, rfl⟩

theorem shiftSecantMinor_mem (N s : ℕ) (hsN : 2 * (s + 1) < N) :
    shiftSecantMinor K N s hsN ∈ RHTower.finiteHankelSecantIdeal K N s :=
  Ideal.subset_span ⟨_, _, fun _ _ h => Nat.succ_lt_succ h, rfl⟩

/-- The nodes `1, …, s` and `0`. -/
def originNodes (s : ℕ) : Fin (s + 1) → K := fun j => if j = Fin.last s then 0 else (j : K) + 1

theorem originNodes_injective [CharZero K] (s : ℕ) : Function.Injective (originNodes K s) := by
  intro a b h
  simp only [originNodes] at h
  by_cases ha : a = Fin.last s <;> by_cases hb : b = Fin.last s
  · rw [ha, hb]
  · rw [if_pos ha, if_neg hb] at h
    exact absurd h.symm (Nat.cast_add_one_ne_zero (b : ℕ))
  · rw [if_neg ha, if_pos hb] at h
    exact absurd h (Nat.cast_add_one_ne_zero (a : ℕ))
  · rw [if_neg ha, if_neg hb] at h
    exact Fin.ext (by exact_mod_cast add_right_cancel h)

theorem leadSecantMinor_notMem [CharZero K] (N s : ℕ) (hsN : 2 * (s + 1) ≤ N) :
    leadSecantMinor K N s hsN ∉ originIdeal K N s := by
  intro hmem
  rw [originIdeal, RingHom.mem_ker] at hmem
  set p : Fin (s + 1) × Fin 2 → K := fun a => if a.2 = 1 then (a.1 : K) + 1 else 1
  have hval := congrArg (MvPolynomial.eval p) hmem
  rw [map_zero, leadSecantMinor, RHTower.finiteHankelMaximalMinorOver, RingHom.map_det,
    RingHom.map_det] at hval
  refine det_atomicHankel_ne_zero K (originNodes_injective K s) (w := fun _ => 1)
    (fun _ => one_ne_zero) ?_
  rw [← hval]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RHTower.finiteHankelIndex, originParam_X,
    map_sum, map_mul, map_pow, MvPolynomial.eval_X, one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [p, originNodes]
  by_cases hj : j = Fin.last s
  · simp [hj]
  · simp [hj]

theorem originParam_X_succ (N s : ℕ) (n : ℕ) (hn : n + 1 < N) :
    originParam K N s (X ⟨n + 1, hn⟩) =
      atomEmbed K s (RHTower.finiteHankelSecantParameterization K N s (X ⟨n + 1, hn⟩)) := by
  rw [originParam_X, RHTower.finiteHankelSecantParameterization_X,
    RHTower.deningerHankelSecantMoment, map_sum, Fin.sum_univ_castSucc, if_pos rfl,
    zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_neg (Fin.castSucc_ne_last j), map_mul, map_pow, atomEmbed, rename_X, rename_X]
  rfl

theorem shiftSecantMinor_mem_originIdeal (N s : ℕ) (hsN : 2 * (s + 1) < N) :
    shiftSecantMinor K N s hsN ∈ originIdeal K N s := by
  have hker := shiftSecantMinor_mem K N s hsN
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker] at hker
  rw [originIdeal, RingHom.mem_ker, shiftSecantMinor, RHTower.finiteHankelMaximalMinorOver,
    RingHom.map_det]
  rw [shiftSecantMinor, RHTower.finiteHankelMaximalMinorOver, RingHom.map_det] at hker
  have h := congrArg (atomEmbed K s) hker
  rw [map_zero, ← AlgHom.coe_toRingHom, RingHom.map_det] at h
  rw [← h]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RHTower.finiteHankelIndex,
    AlgHom.coe_toRingHom]
  exact originParam_X_succ K N s _ _

theorem shiftSecantMinor_notMem [CharZero K] (N s : ℕ) (hsN : 2 * (s + 1) < N) :
    shiftSecantMinor K N s hsN ∉ RHTower.finiteHankelSecantIdeal K N (s + 1) := by
  intro hmem
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker] at hmem
  set τ : Fin (s + 1) → K := fun j => (j : K) + 1
  have hτ : Function.Injective τ := fun a b h => Fin.ext (by exact_mod_cast add_right_cancel h)
  set p : Fin (s + 1) × Fin 2 → K := fun a => if a.2 = 1 then τ a.1 else 1
  have hval := congrArg (MvPolynomial.eval p) hmem
  rw [map_zero, shiftSecantMinor, RHTower.finiteHankelMaximalMinorOver, RingHom.map_det,
    RingHom.map_det] at hval
  refine det_atomicHankel_ne_zero K hτ (w := τ)
    (fun j => Nat.cast_add_one_ne_zero (j : ℕ)) ?_
  rw [← hval]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RHTower.finiteHankelIndex,
    RHTower.finiteHankelSecantParameterization_X, RHTower.deningerHankelSecantMoment, map_sum,
    map_mul, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : p (j, 0) = 1 := if_neg (show (0 : Fin 2) ≠ 1 by decide)
  have h1 : p (j, 1) = τ j := if_pos rfl
  rw [h0, h1, one_mul, ← add_assoc, pow_succ]
  ring

/-- **The singular locus has codimension at least two.**  Every prime of the rank-`(s+1)` secant
ring containing the ideal of maximal `(s+1)`-minors has height at least two. -/
theorem two_le_height_of_singular [CharZero K] {N s : ℕ} (hsN : 2 * (s + 1) < N)
    (P : Ideal (HankelSecantRing K N (s + 1))) [P.IsPrime]
    (hJ : (RHTower.finiteHankelSecantIdeal K N s).map (Ideal.Quotient.mk _) ≤ P) :
    2 ≤ P.height := by
  classical
  set I := RHTower.finiteHankelSecantIdeal K N (s + 1)
  set Q := (originIdeal K N s).map (Ideal.Quotient.mk I) with hQ
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ originIdeal K N s := by
    rw [Ideal.mk_ker]; exact secantIdeal_le_originIdeal K N s
  haveI hQp : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : Q.comap (Ideal.Quotient.mk I) = originIdeal K N s := by
    rw [hQ, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hQP : Q < P := by
    refine lt_of_le_of_ne ((Ideal.map_mono (originIdeal_le_secantIdeal K N s)).trans hJ) ?_
    intro hEq
    have h1 : Ideal.Quotient.mk I (leadSecantMinor K N s hsN.le) ∈ P :=
      hJ (Ideal.mem_map_of_mem _ (leadSecantMinor_mem K N s hsN.le))
    rw [← hEq] at h1
    have h2 : leadSecantMinor K N s hsN.le ∈ Q.comap (Ideal.Quotient.mk I) := h1
    rw [hcomap] at h2
    exact leadSecantMinor_notMem K N s hsN.le h2
  have hbotQ : (⊥ : Ideal (HankelSecantRing K N (s + 1))) < Q := by
    refine bot_lt_iff_ne_bot.mpr fun hQ0 => ?_
    have h1 : Ideal.Quotient.mk I (shiftSecantMinor K N s hsN) ∈ Q :=
      Ideal.mem_map_of_mem _ (shiftSecantMinor_mem_originIdeal K N s hsN)
    rw [hQ0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact shiftSecantMinor_notMem K N s hsN h1
  haveI : (⊥ : Ideal (HankelSecantRing K N (s + 1))).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbotQ
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQP
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Q.height + 1 := by gcongr
    _ ≤ P.height := h2

end

end GaloisForLFunctions.HTGeometry
