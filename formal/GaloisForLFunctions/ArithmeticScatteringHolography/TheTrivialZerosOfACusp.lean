import GaloisForLFunctions.ArithmeticScatteringHolography.TheThroatOfEveryLength
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The trivial zeros of a cusp

Any finite graph with rays. The vertices are `T`, the edge indices are an integer matrix `A`, and `c v` is the total index of the rays at `v`. On a ray the outgoing field is `Y^k`, so the wave equation reduces to the core, and a mode
`X` with `Y = q / X` is a root of the **mode polynomial**

  `R(x) = det((x² + q) I - x A - q diag c)`,

which is monic of degree `2 #T` (`modePoly_monic`, `modePoly_natDegree`), and each nonzero root is a resonance (`exists_field_of_root`). Its value at zero is `R(0) = q^{#T} ∏ (1 - c v)` (`modePoly_coeff_zero`).

**Scaling.** At `x = q w` the whole matrix is divisible by `q`: `R(q w) = q^{#T} S(w)`, with `S` an integer polynomial (`modePoly_scale`). So the coefficient `r_j` of `x^j` satisfies `r_j q^j = q^{#T} s_j` (`coeff_modePoly_mul_pow`).
This is the only input, and it needs nothing about the shape of the graph.

**The law.** Let `R` factor through a ground mode, a functional equation of genus `g`, and compact modes `x² - λ x + q`, with `m` trivial zeros `x²`:

  `R = x^{2m} (x² - q²) L(x²) ∏ (x² - λ x + q)`.

The value of the factors at zero is too small for a large genus, and integrality gives `g ≤ m + 1` (`genus_le_trivial_zeros`). More precisely `|s_{2m}| = q^{m + 1 - g}`. So:

- with no trivial zero, as when the cusp has index `c₀ ≠ 1`, the genus is at most one and `|c₀ - 1| = q^{1-g}` (`cusp_index_law`): index `q + 1` at genus zero, index `2` at genus one, nothing above. This holds for every graph, branched or not;
- from genus two on a cusp must start at a vertex of index one, and it needs at least `g - 1` trivial zeros;
- at such a vertex with one trivial zero, `∑ n_u c_u = q + q^{2-g}` over its neighbours, where `n_u, c_u` are the two indices of the edge (`first_branch_law`). At genus two: `∑ n_u c_u = q + 1`.

Several sectors work the same way: `∑ g_i ≤ m + a` for `a` ground modes and functional equations of genus `g_i` (`total_genus_le_trivial_zeros`).
-/

open Polynomial Matrix Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **The mode matrix of a graph with rays**, over `ℤ[x]`. -/
def modeMatrix (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) : Matrix T T ℤ[X] :=
  Matrix.of fun v u =>
    (if v = u then X ^ 2 + C ((q : ℤ) * (1 - c v)) else 0) - C (A v u) * X

/-- **The mode polynomial.** -/
def modePoly (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) : ℤ[X] := (modeMatrix q A c).det

/-- The scaled matrix: `diag (1 - c) - w A + q w²`. -/
def scaleMatrix (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) : Matrix T T ℤ[X] :=
  Matrix.of fun v u =>
    (if v = u then C (q : ℤ) * X ^ 2 + C (1 - c v) else 0) - C (A v u) * X

theorem quadratic_natDegree {R : Type*} [Ring R] [Nontrivial R] {r : R[X]} (hlow : r.degree < 2) :
    (X ^ 2 + r).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_degree_lt (by simpa using hlow), natDegree_X_pow]

omit [Fintype T] in
theorem modeMatrix_natDegree_le (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) {v u : T} (h : v ≠ u) :
    (modeMatrix q A c v u).natDegree ≤ 1 := by
  simp only [modeMatrix, Matrix.of_apply, if_neg h, zero_sub, natDegree_neg]
  exact (natDegree_C_mul_le _ _).trans natDegree_X_le

omit [Fintype T] in
theorem modeMatrix_diag_monic (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) (v : T) :
    (modeMatrix q A c v v).Monic ∧ (modeMatrix q A c v v).natDegree = 2 := by
  have hform : modeMatrix q A c v v = X ^ 2 + (C (-(A v v)) * X + C ((q : ℤ) * (1 - c v))) := by
    simp only [modeMatrix, Matrix.of_apply, if_true, C_neg]
    ring
  have hlow : (C (-(A v v)) * X + C ((q : ℤ) * (1 - c v))).degree < 2 :=
    lt_of_le_of_lt degree_linear_le (by decide)
  rw [hform]
  exact ⟨monic_X_pow_add hlow, quadratic_natDegree hlow⟩

/-- A determinant with monic quadratic diagonal and off-diagonal entries of degree at most one is monic of twice the size. -/
theorem det_monic_of_quadratic (N : Matrix T T ℤ[X]) (hd : ∀ v, (N v v).Monic ∧ (N v v).natDegree = 2)
    (ho : ∀ v u, v ≠ u → (N v u).natDegree ≤ 1) :
    N.det.Monic ∧ N.det.natDegree = 2 * Fintype.card T := by
  classical
  have hid : (∏ v, N v v).Monic := monic_prod_of_monic _ _ fun v _ => (hd v).1
  have hiddeg : (∏ v, N v v).natDegree = 2 * Fintype.card T := by
    rw [natDegree_prod_of_monic _ _ fun v _ => (hd v).1]
    simp [(hd _).2, Finset.card_univ, mul_comm]
  rcases isEmpty_or_nonempty T with hT | hT
  · have h0 : N.det = 1 := Matrix.det_isEmpty
    rw [h0]
    simp
  have hdet : N.det = ∏ v, N v v +
      ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm T)).erase 1,
        ((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * ∏ v, N (σ v) v := by
    rw [Matrix.det_apply', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm T))]
    simp
  have hpos : 0 < 2 * Fintype.card T := by
    have := Fintype.card_pos (α := T)
    omega
  have hterm (σ : Equiv.Perm T) (hσ : σ ≠ 1) :
      (((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * ∏ v, N (σ v) v).natDegree < 2 * Fintype.card T := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, σ v ≠ v := by
      by_contra h
      exact hσ (Equiv.ext fun v => by_contra fun hv => h ⟨v, hv⟩)
    have hle : ∀ v, (N (σ v) v).natDegree ≤ if σ v = v then 2 else 1 := by
      intro v
      split_ifs with h
      · rw [h]
        exact (hd v).2.le
      · exact ho _ _ h
    have hprod : (∏ v, N (σ v) v).natDegree ≤ ∑ v, (if σ v = v then 2 else 1) :=
      (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun v _ => hle v)
    have hsum : ∑ v, (if σ v = v then 2 else 1) < 2 * Fintype.card T := by
      have : ∑ v : T, (if σ v = v then 2 else 1) < ∑ _v : T, 2 :=
        Finset.sum_lt_sum (fun v _ => by split_ifs <;> omega) ⟨v₀, Finset.mem_univ _, by simp [hv₀]⟩
      simpa [Finset.card_univ, mul_comm] using this
    have hcast : ((Equiv.Perm.sign σ : ℤ) : ℤ[X]) = C ((Equiv.Perm.sign σ : ℤ)) := by simp
    rw [hcast]
    exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans hprod) hsum
  have hrest : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm T)).erase 1,
      ((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * ∏ v, N (σ v) v).degree < (∏ v, N v v).degree := by
    rw [degree_eq_natDegree hid.ne_zero, hiddeg]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
    intro σ hσ
    have hσ1 : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hterm σ hσ1)
  rw [hdet]
  refine ⟨hid.add_of_left hrest, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt hrest, hiddeg]

/-- **The mode polynomial is monic.** -/
theorem modePoly_monic (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) : (modePoly q A c).Monic :=
  (det_monic_of_quadratic _ (modeMatrix_diag_monic q A c) fun _ _ h =>
    modeMatrix_natDegree_le q A c h).1

/-- **It has degree twice the size of the core.** -/
theorem modePoly_natDegree (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) :
    (modePoly q A c).natDegree = 2 * Fintype.card T :=
  (det_monic_of_quadratic _ (modeMatrix_diag_monic q A c) fun _ _ h =>
    modeMatrix_natDegree_le q A c h).2

/-- **The value at zero.** -/
theorem modePoly_coeff_zero (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) :
    (modePoly q A c).coeff 0 = (q : ℤ) ^ Fintype.card T * ∏ v, (1 - c v) := by
  have h := RingHom.map_det (evalRingHom (0 : ℤ)) (modeMatrix q A c)
  have hdiag : (evalRingHom (0 : ℤ)).mapMatrix (modeMatrix q A c) =
      Matrix.diagonal fun v => (q : ℤ) * (1 - c v) := by
    refine Matrix.ext fun v u => ?_
    by_cases hvu : v = u
    · subst hvu
      simp [modeMatrix]
    · simp [modeMatrix, hvu]
  rw [hdiag, Matrix.det_diagonal, Finset.prod_mul_distrib] at h
  rw [coeff_zero_eq_eval_zero, modePoly, ← coe_evalRingHom, h]
  simp [Finset.card_univ]

/-! ### Scaling -/

/-- The scaled determinant `S(w) = det(diag (1 - c) - w A + q w²)`, an integer polynomial. -/
def scalePoly (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) : ℤ[X] := (scaleMatrix q A c).det

/-- **At `x = q w` the matrix is divisible by `q`.** -/
theorem modePoly_scale (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) :
    (modePoly q A c).comp (C (q : ℤ) * X) =
      C ((q : ℤ) ^ Fintype.card T) * scalePoly q A c := by
  have h := RingHom.map_det (compRingHom (C (q : ℤ) * X)) (modeMatrix q A c)
  have hM : (compRingHom (C (q : ℤ) * X)).mapMatrix (modeMatrix q A c) =
      (C (q : ℤ) : ℤ[X]) • scaleMatrix q A c := by
    refine Matrix.ext fun v u => ?_
    by_cases hvu : v = u
    · subst hvu
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, modeMatrix,
        scaleMatrix, Matrix.of_apply, if_true, coe_compRingHom_apply, sub_comp, add_comp, mul_comp,
        pow_comp, X_comp, C_comp, C_mul]
      ring
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, modeMatrix,
        scaleMatrix, Matrix.of_apply, if_neg hvu, coe_compRingHom_apply, sub_comp, mul_comp, X_comp,
        C_comp, zero_comp]
      ring
  rw [hM, Matrix.det_smul] at h
  rw [C_pow, scalePoly, ← coe_compRingHom_apply, modePoly, h]

/-- **The coefficients of the mode polynomial carry a power of `q`.** -/
theorem coeff_modePoly_mul_pow (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) (j : ℕ) :
    (modePoly q A c).coeff j * (q : ℤ) ^ j =
      (q : ℤ) ^ Fintype.card T * (scalePoly q A c).coeff j := by
  rw [← comp_C_mul_X_coeff, modePoly_scale, coeff_C_mul]

/-- **A coefficient of pure size `q^E` at `x^j` forces `#T ≤ E + j`.** -/
theorem card_le_of_coeff {q : ℕ} (hq : 2 ≤ q) (A : Matrix T T ℤ) (c : T → ℤ) {j E : ℕ}
    (h : |(modePoly q A c).coeff j| = (q : ℤ) ^ E) :
    Fintype.card T ≤ E + j ∧
      |(scalePoly q A c).coeff j| * (q : ℤ) ^ Fintype.card T = (q : ℤ) ^ (E + j) := by
  have hrel := congrArg (fun z : ℤ => |z|) (coeff_modePoly_mul_pow q A c j)
  simp only [abs_mul, abs_pow, Nat.abs_cast, h] at hrel
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by linarith
  have hs : |(scalePoly q A c).coeff j| * (q : ℤ) ^ Fintype.card T = (q : ℤ) ^ (E + j) := by
    rw [pow_add, hrel, mul_comm]
  refine ⟨?_, hs⟩
  have hne : |(scalePoly q A c).coeff j| ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact (pow_pos hq0 _).ne hs
  have hone : 1 ≤ |(scalePoly q A c).coeff j| :=
    Int.add_one_le_iff.mpr (lt_of_le_of_ne (abs_nonneg _) hne.symm)
  have hle : (q : ℤ) ^ Fintype.card T ≤ (q : ℤ) ^ (E + j) := by
    rw [← hs]
    exact le_mul_of_one_le_left (pow_pos hq0 _).le hone
  exact (pow_le_pow_iff_right₀ hq1).mp hle

/-! ### Modes -/

/-- The mode polynomial at a complex point. -/
def modeEval (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) (x : ℂ) : ℂ :=
  ((modePoly q A c).map (Int.castRingHom ℂ)).eval x

/-- A root is exactly a nonzero solution of the reduced wave equation. -/
theorem modeEval_eq_zero_iff (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) (x : ℂ) :
    modeEval q A c x = 0 ↔ ∃ f : T → ℂ, f ≠ 0 ∧ ∀ v,
      (x ^ 2 + (q : ℂ) * (1 - (c v : ℂ))) * f v - x * ∑ u, (A v u : ℂ) * f u = 0 := by
  set φ : ℤ[X] →+* ℂ := (evalRingHom x).comp (mapRingHom (Int.castRingHom ℂ)) with hφ
  have h : modeEval q A c x = (φ.mapMatrix (modeMatrix q A c)).det :=
    RingHom.map_det φ (modeMatrix q A c)
  have hentry (v u : T) : φ.mapMatrix (modeMatrix q A c) v u =
      (if v = u then x ^ 2 + (q : ℂ) * (1 - (c v : ℂ)) else 0) - (A v u : ℂ) * x := by
    by_cases hvu : v = u
    · subst hvu
      simp [hφ, modeMatrix]
    · simp [hφ, modeMatrix, hvu]
  have hmul (f : T → ℂ) (v : T) : (φ.mapMatrix (modeMatrix q A c) *ᵥ f) v =
      (x ^ 2 + (q : ℂ) * (1 - (c v : ℂ))) * f v - x * ∑ u, (A v u : ℂ) * f u := by
    simp only [Matrix.mulVec, dotProduct, hentry, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [h, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun f => and_congr_right fun _ => ?_
  rw [funext_iff]
  exact forall_congr' fun v => by rw [hmul, Pi.zero_apply]

/-- **Each nonzero root is a resonance.** With `Y = q / x`, the equation below is the wave equation on the core with the outgoing field `f(v) Y^k` on the rays. -/
theorem exists_field_of_root (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) {x : ℂ} (hx : x ≠ 0)
    (hroot : modeEval q A c x = 0) :
    ∃ f : T → ℂ, f ≠ 0 ∧ ∀ v, ∑ u, (A v u : ℂ) * f u + (c v : ℂ) * ((q : ℂ) / x) * f v =
      (x + (q : ℂ) / x) * f v := by
  obtain ⟨f, hf0, hf⟩ := (modeEval_eq_zero_iff q A c x).mp hroot
  refine ⟨f, hf0, fun v => ?_⟩
  have hv := hf v
  field_simp
  linear_combination -hv

/-- **The ground mode.** If every vertex has `q + 1` edges, then `x = q` is a root: it is the constant function. -/
theorem modeEval_ground [Nonempty T] (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ)
    (hdeg : ∀ v, ∑ u, A v u + c v = q + 1) : modeEval q A c (q : ℂ) = 0 := by
  refine (modeEval_eq_zero_iff q A c _).mpr ⟨fun _ => 1, ?_, fun v => ?_⟩
  · intro h0
    obtain ⟨v⟩ := ‹Nonempty T›
    simpa using congrFun h0 v
  · have h : ∑ u, (A v u : ℂ) + (c v : ℂ) = (q : ℂ) + 1 := by exact_mod_cast hdeg v
    simp only [mul_one]
    linear_combination (-(q : ℂ)) * h

/-- On a bipartite graph `x = -q` is also a root: the alternating function. -/
theorem modeEval_neg_ground [Nonempty T] (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ)
    (hdeg : ∀ v, ∑ u, A v u + c v = q + 1) {ε : T → ℂ} (hε : ∀ v, ε v ≠ 0)
    (hbip : ∀ v u, A v u ≠ 0 → ε u = -ε v) : modeEval q A c (-(q : ℂ)) = 0 := by
  refine (modeEval_eq_zero_iff q A c _).mpr ⟨ε, ?_, fun v => ?_⟩
  · intro h0
    obtain ⟨v⟩ := ‹Nonempty T›
    exact hε v (congrFun h0 v)
  · have h : ∑ u, (A v u : ℂ) + (c v : ℂ) = (q : ℂ) + 1 := by exact_mod_cast hdeg v
    have hsum : ∑ u, (A v u : ℂ) * ε u = -ε v * ∑ u, (A v u : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hvu : A v u = 0
      · simp [hvu]
      · rw [hbip v u hvu]
        ring
    rw [hsum]
    linear_combination (-(q : ℂ) * ε v) * h

/-- **A compact mode.** An eigenfunction of the core that vanishes on the boundary gives the factor `x² - λ x + q`, and this is the form of the compact factors in the law. -/
theorem modeEval_compact (q : ℕ) (A : Matrix T T ℤ) (c : T → ℤ) {l x : ℂ} {f : T → ℂ} (hf0 : f ≠ 0)
    (hf : ∀ v, ∑ u, (A v u : ℂ) * f u = l * f v) (hbd : ∀ v, c v ≠ 0 → f v = 0)
    (hx : x ^ 2 - l * x + q = 0) : modeEval q A c x = 0 := by
  refine (modeEval_eq_zero_iff q A c x).mpr ⟨f, hf0, fun v => ?_⟩
  rw [hf]
  by_cases hc : c v = 0
  · simp only [hc, Int.cast_zero, sub_zero, mul_one]
    linear_combination (f v) * hx
  · rw [hbd v hc]
    ring

/-! ### Factors -/

/-- A compact factor. -/
def compactFactor (q : ℕ) (l : ℂ) : ℂ[X] := X ^ 2 - C l * X + C (q : ℂ)

/-- The product of the compact factors. -/
def compactProd (q : ℕ) (ls : Multiset ℂ) : ℂ[X] := (ls.map (compactFactor q)).prod

theorem compactFactor_spec (q : ℕ) (l : ℂ) :
    (compactFactor q l).Monic ∧ (compactFactor q l).natDegree = 2 ∧
      (compactFactor q l).eval 0 = q := by
  have hform : compactFactor q l = X ^ 2 + (C (-l) * X + C (q : ℂ)) := by
    simp only [compactFactor, C_neg]
    ring
  have hlow : (C (-l) * X + C (q : ℂ)).degree < 2 := lt_of_le_of_lt degree_linear_le (by decide)
  refine ⟨?_, ?_, by simp [compactFactor]⟩
  · rw [hform]
    exact monic_X_pow_add hlow
  · rw [hform]
    exact quadratic_natDegree hlow

theorem compactProd_spec (q : ℕ) (ls : Multiset ℂ) :
    (compactProd q ls).Monic ∧ (compactProd q ls).natDegree = 2 * Multiset.card ls ∧
      (compactProd q ls).eval 0 = (q : ℂ) ^ Multiset.card ls := by
  induction ls using Multiset.induction_on with
  | empty => simp [compactProd]
  | cons l ls ih =>
    obtain ⟨hm, hd, h0⟩ := ih
    obtain ⟨hm', hd', h0'⟩ := compactFactor_spec q l
    have e : compactProd q (l ::ₘ ls) = compactFactor q l * compactProd q ls := by
      simp [compactProd]
    rw [e, Multiset.card_cons]
    refine ⟨hm'.mul hm, ?_, ?_⟩
    · rw [hm'.natDegree_mul hm, hd', hd]
      ring
    · rw [eval_mul, h0', h0]
      ring

/-- A functional equation fixes the value at zero. -/
theorem eval_zero_of_functional_equation {q g : ℕ} (hq : q ≠ 0) {L : ℂ[X]} (hL : L.Monic)
    (hdeg : L.natDegree = 2 * g)
    (hFE : ∀ w : ℂ, w ≠ 0 → L.reverse.eval w = ((q : ℂ) * w ^ 2) ^ g * L.reverse.eval (1 / ((q : ℂ) * w))) :
    L.eval 0 = (q : ℂ) ^ g := by
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hP0 : L.reverse.coeff 0 = 1 := by
    rw [coeff_zero_reverse]
    exact hL.leadingCoeff
  have hPdeg : L.reverse.natDegree ≤ 2 * g := by
    rw [← hdeg]
    exact reverse_natDegree_le L
  have htop := top_of_functional_equation hQ hP0 hPdeg hFE
  have hcoef : L.reverse.coeff (2 * g) = L.eval 0 := by
    rw [reverse, coeff_reflect, hdeg, revAt_le le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
  rw [← hcoef, htop]

theorem comp_spec {L : ℂ[X]} {g : ℕ} (hL : L.Monic) (hdeg : L.natDegree = 2 * g) :
    (L.comp (X ^ 2)).Monic ∧ (L.comp (X ^ 2)).natDegree = 4 * g := by
  refine ⟨hL.comp (monic_X_pow 2) (by simp), ?_⟩
  rw [natDegree_comp, hdeg, natDegree_X_pow]
  ring

theorem ground_spec (q : ℕ) :
    (X ^ 2 - C ((q : ℂ) ^ 2) : ℂ[X]).Monic ∧ (X ^ 2 - C ((q : ℂ) ^ 2) : ℂ[X]).natDegree = 2 :=
  ⟨monic_X_pow_sub_C _ (by norm_num), natDegree_X_pow_sub_C⟩

/-- The degree and the first coefficient read from a factorization with one ground mode. -/
theorem factor_data {q : ℕ} (A : Matrix T T ℤ) (c : T → ℤ) {m g : ℕ} {L : ℂ[X]} {ls : Multiset ℂ}
    (hL : L.Monic) (hdeg : L.natDegree = 2 * g) (hL0 : L.eval 0 = (q : ℂ) ^ g)
    (hfac : (modePoly q A c).map (Int.castRingHom ℂ) =
      X ^ (2 * m) * ((X ^ 2 - C ((q : ℂ) ^ 2)) * (L.comp (X ^ 2) * compactProd q ls))) :
    Fintype.card T = m + 1 + 2 * g + Multiset.card ls ∧
      (modePoly q A c).coeff (2 * m) = -(q : ℤ) ^ (2 + g + Multiset.card ls) := by
  obtain ⟨hKm, hKd, hK0⟩ := compactProd_spec q ls
  obtain ⟨hLc, hLcd⟩ := comp_spec hL hdeg
  obtain ⟨hG, hGd⟩ := ground_spec q
  constructor
  · have h : ((modePoly q A c).map (Int.castRingHom ℂ)).natDegree = 2 * Fintype.card T := by
      rw [(modePoly_monic q A c).natDegree_map, modePoly_natDegree]
    rw [hfac, (monic_X_pow _).natDegree_mul (hG.mul (hLc.mul hKm)), natDegree_X_pow,
      hG.natDegree_mul (hLc.mul hKm), hGd, hLc.natDegree_mul hKm, hLcd, hKd] at h
    omega
  · have h := congrArg (fun p => p.coeff (2 * m)) hfac
    simp only [coeff_map] at h
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero, eval_mul, eval_mul,
      hK0, eval_comp] at h
    simp only [eval_sub, eval_pow, eval_X, eval_C, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_sub, hL0] at h
    have hcast : (((modePoly q A c).coeff (2 * m) : ℤ) : ℂ) =
        ((-(q : ℤ) ^ (2 + g + Multiset.card ls) : ℤ) : ℂ) := by
      refine (by simpa using h : _ = _).trans ?_
      push_cast
      ring
    exact_mod_cast hcast

/-! ### The law -/

/-- **A cusp of genus `g` has at least `g - 1` trivial zeros.** For every finite graph with rays whose mode polynomial is `x^{2m}`, a ground mode, a functional equation of genus `g`, and compact modes. The scaled coefficient has
size `|s_{2m}| q^g = q^{m+1}`. -/
theorem genus_le_trivial_zeros {q : ℕ} (hq : 2 ≤ q) (A : Matrix T T ℤ) (c : T → ℤ) {m g : ℕ} {L : ℂ[X]}
    {ls : Multiset ℂ} (hL : L.Monic) (hdeg : L.natDegree = 2 * g)
    (hFE : ∀ w : ℂ, w ≠ 0 → L.reverse.eval w = ((q : ℂ) * w ^ 2) ^ g * L.reverse.eval (1 / ((q : ℂ) * w)))
    (hfac : (modePoly q A c).map (Int.castRingHom ℂ) =
      X ^ (2 * m) * ((X ^ 2 - C ((q : ℂ) ^ 2)) * (L.comp (X ^ 2) * compactProd q ls))) :
    g ≤ m + 1 ∧ |(scalePoly q A c).coeff (2 * m)| * (q : ℤ) ^ g = (q : ℤ) ^ (m + 1) := by
  have hL0 := eval_zero_of_functional_equation (by omega) hL hdeg hFE
  obtain ⟨hcard, hr⟩ := factor_data A c hL hdeg hL0 hfac
  have habs : |(modePoly q A c).coeff (2 * m)| = (q : ℤ) ^ (2 + g + Multiset.card ls) := by
    rw [hr, abs_neg, abs_pow, Nat.abs_cast]
  obtain ⟨hle, hs⟩ := card_le_of_coeff hq A c habs
  refine ⟨by omega, ?_⟩
  have hq0 : ((q : ℤ) ^ (1 + g + Multiset.card ls + m)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  apply mul_left_cancel₀ hq0
  rw [hcard] at hs
  have e1 : (q : ℤ) ^ (1 + g + Multiset.card ls + m) * (|(scalePoly q A c).coeff (2 * m)| * (q : ℤ) ^ g) =
      |(scalePoly q A c).coeff (2 * m)| * (q : ℤ) ^ (m + 1 + 2 * g + Multiset.card ls) := by ring
  have e2 : (q : ℤ) ^ (1 + g + Multiset.card ls + m) * (q : ℤ) ^ (m + 1) =
      (q : ℤ) ^ (2 + g + Multiset.card ls + 2 * m) := by ring
  rw [e1, e2, hs]

/-- **All sectors.** For `a` ground modes and functional equations of genus `g_i`, up to a root number of norm one, the trivial zeros bound the total genus: `∑ g_i ≤ m + a`. -/
theorem total_genus_le_trivial_zeros {q : ℕ} (hq : 2 ≤ q) (A : Matrix T T ℤ) (c : T → ℤ) {ι : Type*} [Fintype ι]
    {m a : ℕ} {L : ι → ℂ[X]} {g : ι → ℕ} {ls : Multiset ℂ} (hL : ∀ i, (L i).Monic)
    (hdeg : ∀ i, (L i).natDegree = 2 * g i) (hL0 : ∀ i, ‖(L i).eval 0‖ = (q : ℝ) ^ g i)
    (hfac : (modePoly q A c).map (Int.castRingHom ℂ) =
      X ^ (2 * m) * ((X ^ 2 - C ((q : ℂ) ^ 2)) ^ a *
        ((∏ i, (L i).comp (X ^ 2)) * compactProd q ls))) :
    ∑ i, g i ≤ m + a := by
  classical
  obtain ⟨hKm, hKd, hK0⟩ := compactProd_spec q ls
  obtain ⟨hG, hGd⟩ := ground_spec q
  have hLc : ∀ i, ((L i).comp (X ^ 2)).Monic := fun i => (comp_spec (hL i) (hdeg i)).1
  have hLm : (∏ i, (L i).comp (X ^ 2)).Monic := monic_prod_of_monic _ _ fun i _ => hLc i
  have hLd : (∏ i, (L i).comp (X ^ 2)).natDegree = 4 * ∑ i, g i := by
    rw [natDegree_prod_of_monic _ _ fun i _ => hLc i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (comp_spec (hL i) (hdeg i)).2
  have hGa := hG.pow a
  have hcard : Fintype.card T = m + a + 2 * ∑ i, g i + Multiset.card ls := by
    have h : ((modePoly q A c).map (Int.castRingHom ℂ)).natDegree = 2 * Fintype.card T := by
      rw [(modePoly_monic q A c).natDegree_map, modePoly_natDegree]
    rw [hfac, (monic_X_pow _).natDegree_mul (hGa.mul (hLm.mul hKm)), natDegree_X_pow,
      hGa.natDegree_mul (hLm.mul hKm), hG.natDegree_pow, hGd, hLm.natDegree_mul hKm, hLd, hKd] at h
    omega
  have hval : (((modePoly q A c).coeff (2 * m) : ℤ) : ℂ) =
      (-(q : ℂ) ^ 2) ^ a * ((∏ i, (L i).eval 0) * (q : ℂ) ^ Multiset.card ls) := by
    have h := congrArg (fun p => p.coeff (2 * m)) hfac
    simp only [coeff_map] at h
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero, eval_mul, eval_mul,
      hK0, eval_prod, eval_pow] at h
    simp only [eval_comp, eval_sub, eval_pow, eval_X, eval_C, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_sub] at h
    simpa using h
  have habs : |(modePoly q A c).coeff (2 * m)| =
      (q : ℤ) ^ (2 * a + ∑ i, g i + Multiset.card ls) := by
    have hn : ‖(((modePoly q A c).coeff (2 * m) : ℤ) : ℂ)‖ =
        (q : ℝ) ^ (2 * a + ∑ i, g i + Multiset.card ls) := by
      rw [hval, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_pow, norm_prod,
        Finset.prod_congr rfl fun i _ => hL0 i, Finset.prod_pow_eq_pow_sum, Complex.norm_natCast]
      ring
    rw [Complex.norm_intCast] at hn
    exact_mod_cast hn
  have hle := (card_le_of_coeff hq A c habs).1
  omega

/-- **The index law of a cusp.** If no boundary index equals one, there are no trivial zeros, and `(-∏ (1 - c v)) q^g = q`: so the genus is at most one. For one cusp of index `c₀`, this reads `(c₀ - 1) q^g = q`. -/
theorem cusp_index_law {q : ℕ} (hq : 2 ≤ q) (A : Matrix T T ℤ) (c : T → ℤ) {m g : ℕ} {L : ℂ[X]}
    {ls : Multiset ℂ} (hL : L.Monic) (hdeg : L.natDegree = 2 * g)
    (hFE : ∀ w : ℂ, w ≠ 0 → L.reverse.eval w = ((q : ℂ) * w ^ 2) ^ g * L.reverse.eval (1 / ((q : ℂ) * w)))
    (hfac : (modePoly q A c).map (Int.castRingHom ℂ) =
      X ^ (2 * m) * ((X ^ 2 - C ((q : ℂ) ^ 2)) * (L.comp (X ^ 2) * compactProd q ls)))
    (hc : ∀ v, c v ≠ 1) :
    m = 0 ∧ -(∏ v, (1 - c v)) * (q : ℤ) ^ g = q ∧ g ≤ 1 := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hprod : ∏ v, (1 - c v) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => sub_ne_zero.mpr (hc v).symm
  have hm : m = 0 := by
    by_contra hm
    have h := congrArg (fun p => p.coeff 0) hfac
    simp only [coeff_map] at h
    rw [coeff_X_pow_mul', if_neg (by omega), modePoly_coeff_zero] at h
    have h0 : (q : ℤ) ^ Fintype.card T * ∏ v, (1 - c v) = 0 :=
      (map_eq_zero_iff (Int.castRingHom ℂ) Int.cast_injective).mp h
    exact (mul_ne_zero (pow_ne_zero _ hq0) hprod) h0
  subst hm
  have hL0 := eval_zero_of_functional_equation (by omega) hL hdeg hFE
  obtain ⟨hcard, hr⟩ := factor_data A c hL hdeg hL0 hfac
  have hg := (genus_le_trivial_zeros hq A c hL hdeg hFE hfac).1
  refine ⟨rfl, ?_, by omega⟩
  rw [Nat.mul_zero, modePoly_coeff_zero, hcard] at hr
  have hZ : (q : ℤ) ^ (1 + g + Multiset.card ls) ≠ 0 := pow_ne_zero _ hq0
  apply mul_left_cancel₀ hZ
  linear_combination -hr

/-! ### The first branch -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The graph with a distinguished vertex and its neighbours: `n u` edges from the vertex to `u`, `b u` edges back. -/
def branchMatrix (n b : S → ℤ) (A' : Matrix S S ℤ) : Matrix (Unit ⊕ S) (Unit ⊕ S) ℤ :=
  Matrix.fromBlocks 0 (Matrix.of fun _ u => n u) (Matrix.of fun v _ => b v) A'

/-- One ray, with index one, at the distinguished vertex. -/
def branchIndex : Unit ⊕ S → ℤ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- **At a vertex of index one, the mode polynomial starts with `∑ n_u b_u`.** -/
theorem modePoly_branch_coeff_two {q : ℕ} (hq : q ≠ 0) (n b : S → ℤ) (A' : Matrix S S ℤ) :
    (q : ℤ) * (modePoly q (branchMatrix n b A') branchIndex).coeff 2 =
      (q : ℤ) ^ Fintype.card S * ((q : ℤ) - ∑ u, n u * b u) := by
  set N₂ : Matrix (Unit ⊕ S) (Unit ⊕ S) ℤ[X] := Matrix.fromBlocks 1
    (Matrix.of fun _ u => -C (n u)) (Matrix.of fun v _ => -C (b v))
    (Matrix.of fun v u => (if v = u then X ^ 2 + C (q : ℤ) else 0) - C (A' v u) * X) with hN₂
  have hsplit : modeMatrix q (branchMatrix n b A') branchIndex =
      Matrix.diagonal (Sum.elim (fun _ => X) (fun _ => 1)) * N₂ *
        Matrix.diagonal (Sum.elim (fun _ => X) (fun _ => 1)) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with ⟨⟩ | v <;> rcases j with ⟨⟩ | u
    · simp [modeMatrix, branchMatrix, branchIndex, hN₂]
      ring
    · simp [modeMatrix, branchMatrix, branchIndex, hN₂]
      ring
    · simp [modeMatrix, branchMatrix, branchIndex, hN₂]
    · simp [modeMatrix, branchMatrix, branchIndex, hN₂]
  have hdet : modePoly q (branchMatrix n b A') branchIndex = X ^ 2 * N₂.det := by
    rw [modePoly, hsplit, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Fintype.prod_sum_type]
    simp
    ring
  have hcoef : (modePoly q (branchMatrix n b A') branchIndex).coeff 2 = N₂.det.eval 0 := by
    rw [hdet, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  set φ : ℤ[X] →+* ℂ := (Int.castRingHom ℂ).comp (evalRingHom (0 : ℤ)) with hφ
  have hval : ((N₂.det.eval 0 : ℤ) : ℂ) = (φ.mapMatrix N₂).det := RingHom.map_det φ N₂
  have hblock : φ.mapMatrix N₂ = Matrix.fromBlocks 1 (Matrix.of fun _ u => -(n u : ℂ))
      (Matrix.of fun v _ => -(b v : ℂ)) ((q : ℂ) • (1 : Matrix S S ℂ)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with ⟨⟩ | v <;> rcases j with ⟨⟩ | u
    · simp [hN₂, hφ]
    · simp [hN₂, hφ]
    · simp [hN₂, hφ]
    · by_cases hvu : v = u
      · subst hvu
        simp [hN₂, hφ]
      · simp [hN₂, hφ, hvu, Matrix.one_apply_ne hvu]
  letI : Invertible ((q : ℂ) • (1 : Matrix S S ℂ)) :=
    ⟨(q : ℂ)⁻¹ • 1, by simp [smul_smul, hQ], by simp [smul_smul, hQ]⟩
  have hinv : ⅟((q : ℂ) • (1 : Matrix S S ℂ)) = (q : ℂ)⁻¹ • 1 := rfl
  have hschur : (φ.mapMatrix N₂).det = (q : ℂ) ^ Fintype.card S *
      (1 - (q : ℂ)⁻¹ * ∑ u, (n u : ℂ) * (b u : ℂ)) := by
    rw [hblock, Matrix.det_fromBlocks₂₂, hinv, Matrix.det_smul, Matrix.det_one, mul_one,
      Matrix.det_unique]
    congr 1
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hcast : (((q : ℤ) * (modePoly q (branchMatrix n b A') branchIndex).coeff 2 : ℤ) : ℂ) =
      (((q : ℤ) ^ Fintype.card S * ((q : ℤ) - ∑ u, n u * b u) : ℤ) : ℂ) := by
    push_cast
    rw [hcoef, hval, hschur]
    field_simp
  exact_mod_cast hcast

/-- **The first branch law.** A cusp that starts at a vertex of index one with one trivial zero has genus at most two and `(∑ n_u b_u - q) q^g = q²`. At genus two: `∑ n_u b_u = q + 1`. Since `∑ n_u = q`, this says that
`∑ n_u (b_u - 1) = 1`: exactly one neighbour of weight one has index two, and all others have index one. -/
theorem first_branch_law {q : ℕ} (hq : 2 ≤ q) (n b : S → ℤ) (A' : Matrix S S ℤ) {g : ℕ} {L : ℂ[X]}
    {ls : Multiset ℂ} (hL : L.Monic) (hdeg : L.natDegree = 2 * g)
    (hFE : ∀ w : ℂ, w ≠ 0 → L.reverse.eval w = ((q : ℂ) * w ^ 2) ^ g * L.reverse.eval (1 / ((q : ℂ) * w)))
    (hfac : (modePoly q (branchMatrix n b A') branchIndex).map (Int.castRingHom ℂ) =
      X ^ (2 * 1) * ((X ^ 2 - C ((q : ℂ) ^ 2)) * (L.comp (X ^ 2) * compactProd q ls))) :
    (∑ u, n u * b u - (q : ℤ)) * (q : ℤ) ^ g = (q : ℤ) ^ 2 ∧ g ≤ 2 := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hL0 := eval_zero_of_functional_equation (by omega) hL hdeg hFE
  obtain ⟨hcard, hr⟩ := factor_data _ _ hL hdeg hL0 hfac
  have hg := (genus_le_trivial_zeros hq _ _ hL hdeg hFE hfac).1
  refine ⟨?_, by omega⟩
  have hcoef := modePoly_branch_coeff_two (q := q) (by omega) n b A'
  rw [Nat.mul_one] at hr
  rw [hr] at hcoef
  have hS : Fintype.card S = 1 + 2 * g + Multiset.card ls := by
    rw [Fintype.card_sum, Fintype.card_unit] at hcard
    omega
  rw [hS] at hcoef
  have hZ : (q : ℤ) ^ (1 + g + Multiset.card ls) ≠ 0 := pow_ne_zero _ hq0
  apply mul_left_cancel₀ hZ
  linear_combination hcoef

/-- **Calibration.** A single vertex with all its `q + 1` edges in the ray has the mode polynomial `x² - q²`: genus zero, `c₀ = q + 1`. -/
theorem modePoly_single_vertex (q : ℕ) :
    modePoly q (0 : Matrix Unit Unit ℤ) (fun _ => (q : ℤ) + 1) = X ^ 2 - C ((q : ℤ) ^ 2) := by
  rw [modePoly, Matrix.det_unique]
  simp only [modeMatrix, Matrix.of_apply, if_true, Matrix.zero_apply, C_0, zero_mul, sub_zero]
  rw [show (q : ℤ) * (1 - ((q : ℤ) + 1)) = -(q : ℤ) ^ 2 by ring, C_neg]
  ring

end GaloisForLFunctions.ArithmeticScatteringHolography

end
