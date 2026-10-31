import GaloisForLFunctions.AdelicKreinGeometry.ThePoleSuccessorSignatureFormula
import GaloisForLFunctions.AdelicKreinGeometry.EveryPlaceCarriesAPoleSuccessorState
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# Local signatures add over distinct places

A **place assembly** is a sum `Σ_j Φ_j` of pole–successor states at places `v_1, …, v_k`, each with
a conditionally positive conformal successor. On the dilations each `Φ_j` is the hyperbolic pair of
the boost character `χ_j(u) = |u|_{v_j}^{s_j/2}` (`pairKernel_boostChar`).

* **Upper bound** (`negIndex_placeAssembly_le`): `κ ≤ k`, one square per place.
* **Lower bound** (`le_negIndex_placeAssembly`): if one unit `u` separates the `2k` values
  `χ_j(u)^{±1}` and none has modulus one, the pairs carry `k` squares (HKT's exact pair formula).
* **The index of a place assembly** (`negIndex_placeAssembly_eq`): `κ = k`.
* **The real place and a prime** (`negIndex_real_add_padic`): `|a|^{±1/2}` with `−c|b|` and
  `|a|_p^{±1/2}` with `−c'|b|_p` together have exactly two negative squares; the unit `p·r`, `r` a
  second prime, separates them.

So poles at distinct places do not glue: unlike the shared constant direction of a separable
assembly, each place keeps its own square. A global state with one negative square, such as the
pole of `ζ`, is not an assembly of local pole–successor states at two or more places; over `ℚ` the
boosts at the finite places multiply with the archimedean one to `1` only on the principal units.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K]

/-- The boost character `u ↦ |u|_v^{s/2}` of `Kˣ`. -/
def boostChar (v : AbsoluteValue K ℝ) (s : ℝ) : Kˣ →* ℂ where
  toFun u := ((v (u : K) ^ (s / 2) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' u u' := by
    simp only [Units.val_mul, map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _), Complex.ofReal_mul]

theorem boostChar_apply (v : AbsoluteValue K ℝ) (s : ℝ) (u : Kˣ) :
    boostChar v s u = ((v (u : K) ^ (s / 2) : ℝ) : ℂ) := rfl

/-- The boost pair is the pair kernel of the boost character. -/
theorem pairKernel_boostChar (v : AbsoluteValue K ℝ) (s : ℝ) (u : Kˣ) :
    pairKernel (boostChar v s) 1 u = ((v (u : K) ^ (s / 2) + (v (u : K) ^ (s / 2))⁻¹ : ℝ) : ℂ) := by
  simp only [pairKernel, reflectChar_apply, boostChar_apply, one_mul, map_one, Units.val_inv_eq_inv_val,
    map_inv₀, Real.inv_rpow (v.nonneg _), Complex.conj_ofReal, Complex.ofReal_add]

/-- A finite **place assembly** of pole–successor states. -/
def placeAssembly {k : ℕ} (v : Fin k → AbsoluteValue K ℝ) (s : Fin k → ℝ)
    (ψ : Fin k → Multiplicative K → ℂ) (g : AffineGroupOf K) : ℂ :=
  ∑ j, poleSuccessor (v j) (s j) (ψ j) g

/-- Subadditivity of the index over finite sums of Hermitian kernels. -/
theorem negIndex_sum_le {G : Type*} [Group G] {ι : Type*} (S : Finset ι) (f : ι → G → ℂ)
    (hf : ∀ j, IsHermKernel (f j)) :
    negIndex (fun g => ∑ j ∈ S, f j g) ≤ ∑ j ∈ S, negIndex (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty, nonpos_iff_eq_zero]
    exact negIndex_eq_zero_iff.mpr fun n x c => by rw [hermQuad_gram]; simp
  | insert j S hj ih =>
    simp only [sum_insert hj]
    have hS : IsHermKernel fun g => ∑ i ∈ S, f i g := fun g => by
      simp only [map_sum, hf _ g]
    exact (negIndex_add_le (hf j) hS).trans (add_le_add le_rfl ih)

variable {k : ℕ} {v : Fin k → AbsoluteValue K ℝ} {s : Fin k → ℝ}
  {ψ : Fin k → Multiplicative K → ℂ}

/-- **Upper bound**: one square per place. -/
theorem negIndex_placeAssembly_le (hs : ∀ j, 0 < s j) (hv : ∀ j, ∃ u : K, 1 < v j u)
    (hψ : ∀ j, IsConformal (v j) (s j) (ψ j)) (hk : ∀ j, IsHermKernel (ψ j))
    (hpol : ∀ j (n : ℕ) (x : Fin n → Multiplicative K) (c : Fin n → ℂ),
      ∑ a, c a = 0 → 0 ≤ hermQuad (gram (ψ j) x) c) :
    negIndex (placeAssembly v s ψ) ≤ k := by
  have h := negIndex_sum_le univ (fun j => poleSuccessor (v j) (s j) (ψ j))
    fun j => isHermKernel_poleSuccessor (hψ j) (hk j)
  simp only [fun j => negIndex_poleSuccessor (hs j) (hv j) (hψ j) (hpol j), sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

/-- **Lower bound**: a separating unit gives one square per place. -/
theorem le_negIndex_placeAssembly (hs : ∀ j, 0 < s j) (hv : ∀ j, ∃ u : K, 1 < v j u)
    (hψ : ∀ j, IsConformal (v j) (s j) (ψ j)) (u : Kˣ)
    (hne : ∀ j, ‖boostChar (v j) (s j) u‖ ≠ 1)
    (hsep : Function.Injective (nodes (fun j => boostChar (v j) (s j)) u)) :
    (k : ℕ∞) ≤ negIndex (placeAssembly v s ψ) := by
  have hzero : IsPosDefKernel (fun _ : Kˣ => (0 : ℂ)) :=
    ⟨fun _ => by simp, fun n x c => by rw [hermQuad_gram]; simp⟩
  have e : placeAssembly v s ψ ∘ dilationOf =
      fun w => 0 + ∑ j, pairKernel (boostChar (v j) (s j)) 1 w := funext fun w => by
    simp only [Function.comp_apply, placeAssembly, zero_add,
      fun j => poleSuccessor_dilation (hs j) (hv j) (hψ j) w, pairKernel_boostChar]
  have h := negIndex_add_sum_pairKernel_eq hzero (fun j => boostChar (v j) (s j)) (fun _ => 1)
    (fun _ => one_ne_zero) u hne hsep
  rw [← e] at h
  rw [← h]
  exact negIndex_comp_le _ dilationOf

/-- **The index of a place assembly** is the number of places. -/
theorem negIndex_placeAssembly_eq (hs : ∀ j, 0 < s j) (hv : ∀ j, ∃ u : K, 1 < v j u)
    (hψ : ∀ j, IsConformal (v j) (s j) (ψ j)) (hk : ∀ j, IsHermKernel (ψ j))
    (hpol : ∀ j (n : ℕ) (x : Fin n → Multiplicative K) (c : Fin n → ℂ),
      ∑ a, c a = 0 → 0 ≤ hermQuad (gram (ψ j) x) c) (u : Kˣ)
    (hne : ∀ j, ‖boostChar (v j) (s j) u‖ ≠ 1)
    (hsep : Function.Injective (nodes (fun j => boostChar (v j) (s j)) u)) :
    negIndex (placeAssembly v s ψ) = k :=
  le_antisymm (negIndex_placeAssembly_le hs hv hψ hk hpol)
    (le_negIndex_placeAssembly hs hv hψ u hne hsep)

/-! ### The real place and a prime -/

theorem isHermKernel_negUltra (v : AbsoluteValue K ℝ) : IsHermKernel (negUltra v) := fun m => by
  simp [negUltra]

theorem isHermKernel_ofReal_mul {G : Type*} [Group G] {f : G → ℂ} (hf : IsHermKernel f) (c : ℝ) :
    IsHermKernel fun m => (c : ℂ) * f m := fun m => by
  show (c : ℂ) * f m⁻¹ = conj ((c : ℂ) * f m)
  rw [hf m, map_mul, Complex.conj_ofReal]

theorem hermQuad_gram_ofReal_mul_nonneg {G : Type*} [Group G] {f : G → ℂ} {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} (x : Fin n → G) (w : Fin n → ℂ) (h : 0 ≤ hermQuad (gram f x) w) :
    0 ≤ hermQuad (gram (fun m => (c : ℂ) * f m) x) w := by
  have e : gram (fun m => (c : ℂ) * f m) x = (c : ℂ) • gram f x := by ext a b; simp [gram]
  rw [e, hermQuad_smul]
  exact mul_nonneg hc h

section RealAndPrime

variable (p : ℕ) [Fact p.Prime]

/-- The places `∞` and `p` with successors `−c|b|` and `−c'|b|_p`. -/
abbrev realPadicPlaces : Fin 2 → AbsoluteValue ℚ ℝ :=
  ![Rat.AbsoluteValue.real, Rat.AbsoluteValue.padic p]

/-- The unit `p·r`, for a second prime `r`, separates the boosts at `∞` and `p`. -/
theorem injective_nodes_real_padic {r : ℕ} [Fact r.Prime] (hrp : p ≠ r) :
    Function.Injective (nodes (fun j => boostChar (realPadicPlaces p j) ((![1, 1] : Fin 2 → ℝ) j))
      (Units.mk0 ((p * r : ℕ) : ℚ) (by
        have := (Fact.out : p.Prime).pos; have := (Fact.out : r.Prime).pos; positivity))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).one_lt
  have ha : (p : ℝ) < (p : ℝ) * r := by nlinarith
  -- the four node values
  have hreal : Rat.AbsoluteValue.real ((p * r : ℕ) : ℚ) = (p : ℝ) * r := by
    rw [Rat.AbsoluteValue.real_eq_abs, abs_of_nonneg (by positivity)]; simp
  have hpad : Rat.AbsoluteValue.padic p ((p * r : ℕ) : ℚ) = (p : ℝ)⁻¹ := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm, Nat.cast_mul, padicNorm.mul,
      padicNorm.padicNorm_p_of_prime, padicNorm.padicNorm_of_prime_of_ne hrp]
    push_cast; ring
  have hval : ∀ z, nodes (fun j => boostChar (realPadicPlaces p j) ((![1, 1] : Fin 2 → ℝ) j))
      (Units.mk0 ((p * r : ℕ) : ℚ) (by
        have := (Fact.out : p.Prime).pos; have := (Fact.out : r.Prime).pos; positivity)) z =
      ((Sum.elim ![((p : ℝ) * r) ^ (2⁻¹ : ℝ), (p : ℝ) ^ (-2⁻¹ : ℝ)]
        ![((p : ℝ) * r) ^ (-2⁻¹ : ℝ), (p : ℝ) ^ (2⁻¹ : ℝ)] z : ℝ) : ℂ) := by
    rintro (j | j) <;> fin_cases j <;>
      simp (disch := positivity) [nodes, reflectChar_apply, boostChar_apply, realPadicPlaces,
        Units.val_inv_eq_inv_val, map_inv₀, Real.rpow_neg, Real.inv_rpow, Real.mul_rpow,
        padicNorm.padicNorm_of_prime_of_ne hrp, Complex.ofReal_inv, mul_comm]
  -- `(pr)^{−1/2} < p^{−1/2} < 1 < p^{1/2} < (pr)^{1/2}`
  have hp0 : (0 : ℝ) < p := by linarith
  have h12 : (0 : ℝ) < 2⁻¹ := by norm_num
  have i1 : ((p : ℝ) * r) ^ (-2⁻¹ : ℝ) < (p : ℝ) ^ (-2⁻¹ : ℝ) :=
    Real.rpow_lt_rpow_of_neg hp0 ha (by norm_num)
  have i2 : (p : ℝ) ^ (-2⁻¹ : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have i3 : 1 < (p : ℝ) ^ (2⁻¹ : ℝ) := Real.one_lt_rpow hp1 h12
  have i4 : (p : ℝ) ^ (2⁻¹ : ℝ) < ((p : ℝ) * r) ^ (2⁻¹ : ℝ) := Real.rpow_lt_rpow hp0.le ha h12
  intro x y hxy
  rw [hval, hval, Complex.ofReal_inj] at hxy
  rcases x with (x | x) <;> rcases y with (y | y) <;> fin_cases x <;> fin_cases y <;>
    first | rfl | (simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] at hxy; linarith)

/-- **Two places, two squares**: the archimedean and the `p`-adic pole–successor states together
have exactly two negative squares. -/
theorem negIndex_real_add_padic {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    negIndex (placeAssembly (realPadicPlaces p) ![1, 1]
      ![fun m => (c : ℂ) * negAbsRat m,
        fun m => (c' : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m]) = 2 := by
  -- a second prime
  obtain ⟨r, hr, hrp⟩ : ∃ r : ℕ, r.Prime ∧ p ≠ r := by
    by_cases h2 : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, h2⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr.one_lt
  have hu : ((p * r : ℕ) : ℚ) ≠ 0 := by
    have := (Fact.out : p.Prime).pos; have := hr.pos; positivity
  have h := negIndex_placeAssembly_eq (v := realPadicPlaces p) (s := ![1, 1])
    (ψ := ![fun m => (c : ℂ) * negAbsRat m,
      fun m => (c' : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m])
    (fun j => by fin_cases j <;> norm_num)
    (fun j => by
      fin_cases j
      · exact exists_one_lt_real
      · exact ⟨_, one_lt_padic_inv p⟩)
    (fun j => by
      fin_cases j
      · exact isConformal_negAbsRat c
      · exact isConformal_negUltra _ c')
    (fun j => by
      fin_cases j
      · exact isHermKernel_ofReal_mul isHermKernel_negAbsRat c
      · exact isHermKernel_ofReal_mul (isHermKernel_negUltra _) c')
    (fun j n x w hw => by
      fin_cases j
      · exact hermQuad_gram_ofReal_mul_nonneg hc x w (hermQuad_gram_negAbsRat_nonneg x w hw)
      · exact hermQuad_gram_ofReal_mul_nonneg hc' x w
          (hermQuad_gram_negUltra_nonneg (isUltra_padic p) x w hw))
    (Units.mk0 _ hu)
    (by
      have hreal : Rat.AbsoluteValue.real ((p * r : ℕ) : ℚ) = ((p * r : ℕ) : ℝ) := by
        rw [Rat.AbsoluteValue.real_eq_abs, abs_of_nonneg (by positivity)]; simp
      have hpad : Rat.AbsoluteValue.padic p ((p * r : ℕ) : ℚ) = (p : ℝ)⁻¹ := by
        rw [Rat.AbsoluteValue.padic_eq_padicNorm, Nat.cast_mul, padicNorm.mul,
          padicNorm.padicNorm_p_of_prime, padicNorm.padicNorm_of_prime_of_ne hrp]
        push_cast; ring
      have hpr : (1 : ℝ) < ((p * r : ℕ) : ℝ) := by push_cast; nlinarith
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [boostChar_apply, realPadicPlaces, Units.val_mk0, Matrix.cons_val_zero, hreal,
          Complex.norm_real]
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        exact (Real.one_lt_rpow hpr (by norm_num)).ne'
      · simp only [boostChar_apply, realPadicPlaces, Units.val_mk0, Matrix.cons_val_one,
          Matrix.cons_val_zero, hpad, Complex.norm_real]
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)]
        exact (Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1) (by norm_num)).ne)
    (injective_nodes_real_padic p hrp)
  simpa using h

end RealAndPrime

end GaloisForLFunctions.AdelicKreinGeometry
