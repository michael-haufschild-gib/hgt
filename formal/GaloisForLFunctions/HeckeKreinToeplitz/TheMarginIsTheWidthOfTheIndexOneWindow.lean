import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveMarginIsTwoLogTwo

/-!
# The margin `2 log 2` is the width of the index-one window

The multiplicative Poincaré inequality in index language. Weil's prime kernel is a Hermitian kernel
on `ℚ_{>0}` (`primeKernel`: `Λ(r) r^{−1/2}` at `r^{±1}`, `r ≥ 2` an integer). At atomic resolution
the archimedean place contributes a diagonal counterterm `D`, and the atomic kernel is
`A_D = D δ₁ − P` (`atomKernel`); its Gram matrix on the integers `1, …, N` is `D·1 − P_N`
(`gram_atomKernel`).

**The index ladder.** For every `ε > 0`, eventually in `N`, with `L = log N − γ`:

* `κ_N(D) = 0` for `D ≥ L + ε` (`eventually_hermNegIndex_atom_eq_zero`, the Robin–Euler ceiling);
* `κ_N(D) = 1` for `L − 2 log 2 + ε ≤ D < L − ε` (`eventually_hermNegIndex_atom_eq_one`), and the
  negative square is carried by the pole: the form is nonnegative on the pole hyperplane
  `Σ c_n n^{−1/2} = 0` (`eventually_hermQuad_atom_nonneg_on_pole`);
* `κ_N(D) ≥ 2` for `D < L − 2 log 2 − ε` (`eventually_two_le_hermNegIndex_atom`): the second square
  is the conductor-`2` Ramanujan mode at energy `γ + 2 log 2`.

Beyond the bottom: every adjunction energy `E_m = γ + log m + τ(m)` is a rung, and the index is at
least the number of separated rungs below `log N − D` (`eventually_card_le_hermNegIndex_atom`).
The pole is the rung `m = 1`; conductor `2` is the first rung above it, since `E_m > E₂` for every
`m ≥ 3` (`ramanujanAdjunctionEnergy_two_lt`). This is why `2` sets the margin.

So the margin `2 log 2` is the width of the window of counterterms on which the atomic kernel has
exactly one negative square.

**Twin-blind index, selective carrier.** A sign gauge `ω` (`ω² = 1`) acts by congruence, so every
twin has the same index ladder (`hermNegIndex_gaugeAtom_eq`). What selects `ζ` is where the square
sits. For every sign gauge the pole stops carrying it below `L − 2 log 2`
(`eventually_exists_neg_on_pole_gauge`), so `ζ` is optimal; for the Liouville twin it is never
carried below `L` (`eventually_exists_neg_on_pole_liouville`).

**Why the gap does not bound the index** (`negIndex_atomKernel_eq_top`). At every fixed counterterm
the atomic kernel has infinitely many negative squares on `ℚ_{>0}`: one negative window, translated
by distinct primes beyond it, gives mutually orthogonal negative vectors
(`card_le_negIndex_of_orthogonal_translates`). The margin is a statement about finite windows with
a growing counterterm `log N − γ − 2 log 2`; it can never be an index ceiling for a kernel on the
whole lattice.
-/

open Complex Finset Filter Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (negIndex_le_card_of_nonneg_on_ker)
open GaloisForLFunctions.ArithmeticEffectivityTheory (weilPrimeKernel)
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm)
open GaloisForLFunctions.ArithmeticIntersectionTheory (weilPrimeKernel_symm)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex fullPrimeMatrix
  fullPrimeMatrix_isHermitian eventually_fullPrimeMatrix_eigenvalue_near
  eventually_atomicWeilForm_add_poleDefect_le eventually_atomicWeilForm_le_two_log_two
  poleDefect_nonneg exists_pole_hyperplane_separates_liouville liouvilleSign liouvilleSign_mul_self)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (ramanujanAdjunctionEnergy)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (horizonExtend horizonExtend_coe
  sum_horizonExtend atomicWeilForm_horizonExtend sum_eigenvector_mul ramanujanAdjunctionEnergy_one
  ramanujanAdjunctionEnergy_two eventually_forall_exists_orthogonal_atomicWeilForm_ge
  two_mul_log_two_lt_log_add_tameDifferent)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Orthogonal translates -/

section Translates

variable {G : Type*} [Group G]

/-- **Orthogonal translates multiply the index.** If `c` is a negative vector of `k` on the family
`x`, and the translates `g_j x` are mutually `k`-orthogonal, then `k` has at least as many negative
squares as there are translates. -/
theorem card_le_negIndex_of_orthogonal_translates {k : G → ℂ} {ι J : Type*} [Fintype ι]
    [Fintype J] [DecidableEq J] {x : ι → G} {c : ι → ℂ} (hc : hermQuad (gram k x) c < 0)
    (g : J → G) (horth : ∀ j j', j ≠ j' → ∀ a b, k ((g j * x a)⁻¹ * (g j' * x b)) = 0) :
    (Fintype.card J : ℕ∞) ≤ negIndex k := by
  set y : J × ι → G := fun p => g p.1 * x p.2
  let L : (J → ℂ) →ₗ[ℂ] (J × ι → ℂ) :=
    { toFun := fun β p => β p.1 * c p.2
      map_add' := fun β β' => funext fun p => add_mul _ _ _
      map_smul' := fun t β => funext fun p => mul_assoc _ _ _ }
  have hmul : ∀ β j a, (gram k y *ᵥ L β) (j, a) = β j * (gram k x *ᵥ c) a := fun β j a => by
    simp only [mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j, Finset.mul_sum]
    · refine sum_congr rfl fun b _ => ?_
      simp only [gram, y, L, LinearMap.coe_mk, AddHom.coe_mk, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
      ring
    · intro j' _ hj'
      refine sum_eq_zero fun b _ => ?_
      simp only [gram, y]
      rw [horth j j' (Ne.symm hj') a b, zero_mul]
    · exact fun h => absurd (mem_univ j) h
  have hq : ∀ β, hermQuad (gram k y) (L β) = ∑ j, normSq (β j) * hermQuad (gram k x) c := by
    intro β
    simp only [hermQuad, dotProduct, Pi.star_apply, Fintype.sum_prod_type, hmul]
    rw [re_sum]
    refine sum_congr rfl fun j _ => ?_
    have : ∀ a, star (L β (j, a)) * (β j * (gram k x *ᵥ c) a) =
        (normSq (β j) : ℂ) * (star (c a) * (gram k x *ᵥ c) a) := fun a => by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, star_mul', normSq_eq_conj_mul_self,
        RCLike.star_def]
      ring
    simp only [this, ← mul_sum, re_ofReal_mul]
  have h := card_le_hermNegIndex_of_forall_neg (gram k y) L fun β hβ => by
    obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (funext h)
    rw [hq]
    have := Finset.sum_lt_sum (s := univ) (f := fun j => normSq (β j) * hermQuad (gram k x) c)
      (g := fun _ => 0) (fun j _ => mul_nonpos_of_nonneg_of_nonpos (normSq_nonneg _) hc.le)
      ⟨j, mem_univ _, mul_neg_of_pos_of_neg (normSq_pos.mpr hj) hc⟩
    simpa using this
  exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex k y)

end Translates

/-! ### Weil's prime kernel on `ℚ_{>0}` -/

/-- Weil's prime kernel depends only on the ratio `n/m`. -/
theorem weilPrimeKernel_mul_left {d : ℕ} (hd : 0 < d) (m n : ℕ) :
    weilPrimeKernel (d * m) (d * n) = weilPrimeKernel m n := by
  have h : d * m = d * n ↔ m = n := Nat.mul_left_cancel_iff hd
  have h' : d * n = d * m ↔ n = m := Nat.mul_left_cancel_iff hd
  unfold weilPrimeKernel
  simp only [Nat.mul_dvd_mul_iff_left hd, Nat.mul_div_mul_left _ _ hd, ne_eq, h, h']

theorem weilPrimeKernel_eq_of_mul_eq {a b m n : ℕ} (ha : 0 < a) (hm : 0 < m) (h : b * m = n * a) :
    weilPrimeKernel a b = weilPrimeKernel m n := by
  rw [← weilPrimeKernel_mul_left hm a b, ← weilPrimeKernel_mul_left ha m n, mul_comm m b, h,
    mul_comm m a, mul_comm n a]

/-- Weil's prime kernel vanishes on pairs neither of which divides the other. -/
theorem weilPrimeKernel_eq_zero {m n : ℕ} (h₁ : ¬ m ∣ n) (h₂ : ¬ n ∣ m) : weilPrimeKernel m n = 0 := by
  unfold weilPrimeKernel
  rw [if_neg fun h => h₁ h.1, if_neg fun h => h₂ h.1]

theorem weilPrimeKernel_den_num {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    weilPrimeKernel ((b : ℚ) / a).den ((b : ℚ) / a).num.toNat = weilPrimeKernel a b := by
  set q : ℚ := (b : ℚ) / a
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hnum : 0 < q.num := Rat.num_pos.mpr (by positivity)
  have h2 : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  have key : (b : ℚ) * q.den = q * q.den * a := by
    rw [mul_comm q, mul_assoc, show q * a = b from div_mul_cancel₀ _ ha', mul_comm]
  have hcross : b * q.den = q.num.toNat * a := by
    have : ((b * q.den : ℕ) : ℚ) = ((q.num.toNat * a : ℕ) : ℚ) := by
      push_cast
      rw [h2, ← Rat.mul_den_eq_num, key]
    exact_mod_cast this
  exact (weilPrimeKernel_eq_of_mul_eq ha (Rat.den_pos q) hcross).symm

/-- **Weil's prime kernel on `ℚ_{>0}`**: `Λ(r) r^{−1/2}` at `r` and at `1/r` for integers `r ≥ 2`,
zero elsewhere. -/
def primeKernel (u : HeckeLattice) : ℂ := weilPrimeKernel (u : ℚ).den (u : ℚ).num.toNat

theorem primeKernel_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {u : HeckeLattice}
    (hu : (u : ℚ) = b / a) : primeKernel u = weilPrimeKernel a b := by
  rw [primeKernel, hu, weilPrimeKernel_den_num ha hb]

theorem isHermKernel_primeKernel : IsHermKernel primeKernel := fun u => by
  have hnum : 0 < (u : ℚ).num := Rat.num_pos.mpr u.2
  have hu : (u : ℚ) = ((u : ℚ).num.toNat : ℕ) / ((u : ℚ).den : ℕ) := by
    rw [show (((u : ℚ).num.toNat : ℕ) : ℚ) = (u : ℚ).num by
      exact_mod_cast Int.toNat_of_nonneg hnum.le, Rat.num_div_den]
  have hb : 0 < (u : ℚ).num.toNat := by omega
  have ha : 0 < (u : ℚ).den := Rat.den_pos _
  generalize (u : ℚ).num.toNat = b at hu hb
  generalize (u : ℚ).den = a at hu ha
  have hinv : ((u⁻¹ : HeckeLattice) : ℚ) = a / b := by
    rw [show ((u⁻¹ : HeckeLattice) : ℚ) = (u : ℚ)⁻¹ from rfl, hu, inv_div]
  rw [primeKernel_eq hb ha hinv, primeKernel_eq ha hb hu, weilPrimeKernel_symm, conj_ofReal]

/-- The **atomic kernel** at counterterm `D`: `D δ₁ − P` on `ℚ_{>0}`. -/
def atomKernel (D : ℝ) (u : HeckeLattice) : ℂ := (if u = 1 then (D : ℂ) else 0) - primeKernel u

theorem atomKernel_eq (D : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {u : HeckeLattice}
    (hu : (u : ℚ) = b / a) :
    atomKernel D u = (((if a = b then D else 0) - weilPrimeKernel a b : ℝ) : ℂ) := by
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have h1 : u = 1 ↔ a = b := by
    rw [← Subtype.coe_inj, show ((1 : HeckeLattice) : ℚ) = 1 from rfl, hu, div_eq_one_iff_eq ha',
      Nat.cast_inj, eq_comm]
  rw [atomKernel, primeKernel_eq ha hb hu]
  by_cases h : a = b <;> simp [h, h1]

/-! ### The atomic Gram matrix on the integer horizon -/

/-- The integers `1, …, N` in `ℚ_{>0}`. -/
def horizonPoint (N : ℕ) (n : PrimeHorizonIndex N) : HeckeLattice :=
  ⟨((n : ℕ) : ℚ), by have := (mem_Icc.mp n.2).1; positivity⟩

/-- The atomic matrix `D·1 − P_N` on `{1, …, N}`. -/
def atomMatrix (N : ℕ) (D : ℝ) : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  D • 1 - fullPrimeMatrix N

theorem gram_atomKernel (N : ℕ) (D : ℝ) :
    gram (atomKernel D) (horizonPoint N) = (atomMatrix N D).map (↑) := by
  ext n j
  have hn := (mem_Icc.mp n.2).1
  have hj := (mem_Icc.mp j.2).1
  rw [gram, atomKernel_eq D hn hj (u := (horizonPoint N n)⁻¹ * horizonPoint N j)
    (by show ((n : ℕ) : ℚ)⁻¹ * ((j : ℕ) : ℚ) = _; rw [inv_mul_eq_div])]
  by_cases h : (n : ℕ) = j
  · have h' : n = j := Subtype.ext h
    subst h'
    simp [atomMatrix, fullPrimeMatrix]
  · have h' : n ≠ j := fun e => h (congrArg Subtype.val e)
    simp [atomMatrix, fullPrimeMatrix, h, h']

/-- The Hermitian form of a real matrix splits over the real and imaginary parts. -/
theorem hermQuad_map_ofReal {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (c : ι → ℂ) :
    hermQuad (B.map (↑)) c = (fun i => (c i).re) ⬝ᵥ (B *ᵥ fun i => (c i).re) +
      (fun i => (c i).im) ⬝ᵥ (B *ᵥ fun i => (c i).im) := by
  simp only [hermQuad, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum, re_sum,
    ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, mul_re, mul_im, conj_re, conj_im, ofReal_re,
    ofReal_im]
  ring

theorem hermQuad_map_ofReal_real {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (y : ι → ℝ) :
    hermQuad (B.map (↑)) (fun i => (y i : ℂ)) = y ⬝ᵥ (B *ᵥ y) := by
  rw [hermQuad_map_ofReal]
  simp [dotProduct, mulVec]

/-- The real atomic form in the coordinates of the prime form. -/
theorem atomQuad_eq (N : ℕ) (D : ℝ) (y : PrimeHorizonIndex N → ℝ) :
    y ⬝ᵥ (atomMatrix N D *ᵥ y) =
      D * ∑ n ∈ Icc 1 N, horizonExtend y n ^ 2 - atomicWeilForm N (horizonExtend y) := by
  rw [atomicWeilForm_horizonExtend, sum_horizonExtend y (fun _ t => t ^ 2), atomMatrix,
    Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct, sq]

/-- The **pole functional** `c ↦ Σ_n c_n n^{−1/2}`; its kernel is the pole hyperplane. -/
def poleFunctional (N : ℕ) : (PrimeHorizonIndex N → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ n, c n * ((Real.sqrt (n : ℕ))⁻¹ : ℝ)
  map_add' c d := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, RingHom.id_apply]

theorem sum_horizonExtend_div_sqrt {N : ℕ} (y : PrimeHorizonIndex N → ℝ) :
    ∑ n ∈ Icc 1 N, horizonExtend y n / Real.sqrt n = ∑ n, y n * (Real.sqrt (n : ℕ))⁻¹ := by
  rw [sum_horizonExtend y (fun n t => t / Real.sqrt n)]
  simp only [div_eq_mul_inv]

theorem re_poleFunctional {N : ℕ} (c : PrimeHorizonIndex N → ℂ) :
    (poleFunctional N c).re = ∑ n, (c n).re * (Real.sqrt (n : ℕ))⁻¹ := by
  simp only [poleFunctional, LinearMap.coe_mk, AddHom.coe_mk, re_sum, mul_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero]

theorem im_poleFunctional {N : ℕ} (c : PrimeHorizonIndex N → ℂ) :
    (poleFunctional N c).im = ∑ n, (c n).im * (Real.sqrt (n : ℕ))⁻¹ := by
  simp only [poleFunctional, LinearMap.coe_mk, AddHom.coe_mk, im_sum, mul_im, ofReal_re, ofReal_im,
    mul_zero, zero_add]

/-! ### The index ladder -/

/-- **Above the Robin–Euler point the atomic kernel is positive.** -/
theorem eventually_hermNegIndex_atom_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ + ε ≤ D →
      hermNegIndex (gram (atomKernel D) (horizonPoint N)) = 0 := by
  set ε₁ := min ε (1 / 2)
  obtain ⟨N₀, h⟩ := eventually_atomicWeilForm_add_poleDefect_le (lt_min hε (by norm_num) : 0 < ε₁)
  filter_upwards [eventually_ge_atTop N₀] with N hN D hD
  have hQ : ∀ y : PrimeHorizonIndex N → ℝ, 0 ≤ y ⬝ᵥ (atomMatrix N D *ᵥ y) := fun y => by
    rw [atomQuad_eq]
    have h1 := h N hN (horizonExtend y)
    have hS : 0 ≤ ∑ n ∈ Icc 1 N, horizonExtend y n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have h2 : 0 ≤ (1 - ε₁) * GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.poleDefect N
        (horizonExtend y) :=
      mul_nonneg (by linarith [min_le_right ε (1 / 2)]) (poleDefect_nonneg N _)
    have h3 := mul_le_mul_of_nonneg_right (min_le_left ε (1 / 2)) hS
    have h4 := mul_le_mul_of_nonneg_right hD hS
    nlinarith
  have := negIndex_le_card_of_nonneg_on_ker (gram (atomKernel D) (horizonPoint N))
    (fun i : Fin 0 => i.elim0) fun c _ => by
      rw [gram_atomKernel, hermQuad_map_ofReal]
      exact add_nonneg (hQ _) (hQ _)
  simpa using this

/-- **Above `log N − γ − 2 log 2` the pole carries the index.** The atomic form is nonnegative on
the pole hyperplane. -/
theorem eventually_hermQuad_atom_nonneg_on_pole {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - 2 * Real.log 2 + ε ≤ D →
      ∀ c, poleFunctional N c = 0 → 0 ≤ hermQuad (gram (atomKernel D) (horizonPoint N)) c := by
  obtain ⟨N₀, h⟩ := eventually_atomicWeilForm_le_two_log_two hε
  filter_upwards [eventually_ge_atTop N₀] with N hN D hD c hc
  have key : ∀ y : PrimeHorizonIndex N → ℝ, ∑ n, y n * (Real.sqrt (n : ℕ))⁻¹ = 0 →
      0 ≤ y ⬝ᵥ (atomMatrix N D *ᵥ y) := fun y hy => by
    rw [atomQuad_eq]
    have h1 := h N hN _ (by rw [sum_horizonExtend_div_sqrt]; exact hy)
    have hS : 0 ≤ ∑ n ∈ Icc 1 N, horizonExtend y n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hD hS]
  rw [gram_atomKernel, hermQuad_map_ofReal]
  refine add_nonneg (key _ ?_) (key _ ?_)
  · rw [← re_poleFunctional, hc, zero_re]
  · rw [← im_poleFunctional, hc, zero_im]

/-- Above `log N − γ − 2 log 2` the atomic kernel has at most one negative square. -/
theorem eventually_hermNegIndex_atom_le_one {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - 2 * Real.log 2 + ε ≤ D →
      hermNegIndex (gram (atomKernel D) (horizonPoint N)) ≤ 1 := by
  filter_upwards [eventually_hermQuad_atom_nonneg_on_pole hε] with N h D hD
  simpa using negIndex_le_card_of_nonneg_on_ker (gram (atomKernel D) (horizonPoint N))
    (fun _ : Fin 1 => poleFunctional N) fun c hc => h D hD c (hc 0)

/-- On a span of distinct eigenvectors of `P_N` the atomic form is diagonal. -/
theorem hermQuad_atom_eigen {N k : ℕ} (D : ℝ) {s : Fin k → PrimeHorizonIndex N}
    (hs : Function.Injective s) (a : Fin k → ℂ) :
    hermQuad ((atomMatrix N D).map (↑)) (∑ t, a t • fun n =>
        (((fullPrimeMatrix_isHermitian N).eigenvectorBasis (s t) n : ℝ) : ℂ)) =
      ∑ t, normSq (a t) * (D - (fullPrimeMatrix_isHermitian N).eigenvalues (s t)) := by
  set e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis
  set lam := (fullPrimeMatrix_isHermitian N).eigenvalues
  have hM : ∀ i, atomMatrix N D *ᵥ ⇑(e i) = (D - lam i) • ⇑(e i) := fun i => by
    rw [atomMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      (fullPrimeMatrix_isHermitian N).mulVec_eigenvectorBasis, sub_smul]
  have horth : ∀ t u, ⇑(e (s t)) ⬝ᵥ ⇑(e (s u)) = if t = u then 1 else 0 := fun t u => by
    rw [dotProduct]
    exact (sum_eigenvector_mul (s t) (s u)).trans (by simp only [hs.eq_iff])
  have hdot : ∀ f g : Fin k → ℝ, (∑ t, f t • ⇑(e (s t))) ⬝ᵥ (∑ u, g u • ⇑(e (s u))) =
      ∑ t, f t * g t := fun f g => by
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    have : ∀ u, ∑ n, f t * e (s t) n * (g u * e (s u) n) = f t * g u * (if t = u then 1 else 0) :=
      fun u => by
        rw [← horth t u, dotProduct, Finset.mul_sum]
        exact sum_congr rfl fun n _ => by ring
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
  have hreal : ∀ r : Fin k → ℝ, (∑ t, r t • ⇑(e (s t))) ⬝ᵥ (atomMatrix N D *ᵥ ∑ t, r t • ⇑(e (s t))) =
      ∑ t, r t ^ 2 * (D - lam (s t)) := fun r => by
    have hv : atomMatrix N D *ᵥ ∑ t, r t • ⇑(e (s t)) =
        ∑ u, (r u * (D - lam (s u))) • ⇑(e (s u)) := by
      rw [Matrix.mulVec_sum]
      exact sum_congr rfl fun u _ => by rw [Matrix.mulVec_smul, hM, smul_smul]
    rw [hv, hdot]
    exact sum_congr rfl fun t _ => by ring
  have hre : (fun n => ((∑ t, a t • fun n => ((e (s t) n : ℝ) : ℂ)) n).re) =
      ∑ t, (a t).re • ⇑(e (s t)) := funext fun n => by
    simp [Finset.sum_apply, re_sum]
  have him : (fun n => ((∑ t, a t • fun n => ((e (s t) n : ℝ) : ℂ)) n).im) =
      ∑ t, (a t).im • ⇑(e (s t)) := funext fun n => by
    simp [Finset.sum_apply, im_sum]
  rw [hermQuad_map_ofReal, hre, him, hreal, hreal, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [normSq_apply]
  ring

/-- Distinct eigenvalues of `P_N` above `D` give as many negative squares of the atomic kernel. -/
theorem le_hermNegIndex_atom_of_eigen {N k : ℕ} {D : ℝ} {s : Fin k → PrimeHorizonIndex N}
    (hs : Function.Injective s) (h : ∀ t, D < (fullPrimeMatrix_isHermitian N).eigenvalues (s t)) :
    k ≤ hermNegIndex (gram (atomKernel D) (horizonPoint N)) := by
  have := card_le_hermNegIndex_of_forall_neg (gram (atomKernel D) (horizonPoint N))
    (Fintype.linearCombination ℂ fun t n =>
      (((fullPrimeMatrix_isHermitian N).eigenvectorBasis (s t) n : ℝ) : ℂ)) fun a ha => by
    rw [Fintype.linearCombination_apply, gram_atomKernel, hermQuad_atom_eigen D hs a]
    obtain ⟨t, ht⟩ : ∃ t, a t ≠ 0 := by
      by_contra hc
      push Not at hc
      exact ha (funext hc)
    have := Finset.sum_lt_sum (s := univ)
      (f := fun t => normSq (a t) * (D - (fullPrimeMatrix_isHermitian N).eigenvalues (s t)))
      (g := fun _ => 0) (fun u _ => mul_nonpos_of_nonneg_of_nonpos (normSq_nonneg _)
        (by linarith [h u]))
      ⟨t, mem_univ _, mul_neg_of_pos_of_neg (normSq_pos.mpr ht) (by linarith [h t])⟩
    simpa using this
  simpa using this

/-- **Below the Robin–Euler point the atomic kernel has a negative square**: the top eigenvalue of
`P_N` is `log N − γ + o(1)`. -/
theorem eventually_one_le_hermNegIndex_atom {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - ε →
      1 ≤ hermNegIndex (gram (atomKernel D) (horizonPoint N)) := by
  filter_upwards [eventually_fullPrimeMatrix_eigenvalue_near one_pos hε] with N hN D hD
  obtain ⟨i, hi⟩ := hN
  rw [ramanujanAdjunctionEnergy_one] at hi
  have hi' := (abs_lt.mp hi).1
  exact le_hermNegIndex_atom_of_eigen (s := fun _ : Fin 1 => i)
    (fun a b _ => Subsingleton.elim a b) fun _ => by linarith

/-- **Below `log N − γ − 2 log 2` the atomic kernel has two negative squares**: the conductor-`2`
Ramanujan mode is the second eigenvalue, at `log N − γ − 2 log 2 + o(1)`. -/
theorem eventually_two_le_hermNegIndex_atom {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - 2 * Real.log 2 - ε →
      2 ≤ hermNegIndex (gram (atomKernel D) (horizonPoint N)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set δ := min ε (Real.log 2 / 2)
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδl : δ ≤ Real.log 2 / 2 := min_le_right _ _
  filter_upwards [eventually_fullPrimeMatrix_eigenvalue_near one_pos hδ,
    eventually_fullPrimeMatrix_eigenvalue_near two_pos hδ] with N h₁ h₂ D hD
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  rw [ramanujanAdjunctionEnergy_one] at hi
  rw [ramanujanAdjunctionEnergy_two] at hj
  have hi' := abs_lt.mp hi
  have hj' := abs_lt.mp hj
  have hij : i ≠ j := fun h => by rw [h] at hi'; linarith
  refine le_hermNegIndex_atom_of_eigen (s := ![i, j]) (fun a b hab => ?_) fun t => ?_
  · fin_cases a <;> fin_cases b <;> simp_all
  · fin_cases t <;> simp <;> linarith

/-- **The index-one window.** For `log N − γ − 2 log 2 + ε ≤ D < log N − γ − ε` the atomic kernel
has exactly one negative square, carried by the pole. -/
theorem eventually_hermNegIndex_atom_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - 2 * Real.log 2 + ε ≤ D →
      D < Real.log N - γ - ε → hermNegIndex (gram (atomKernel D) (horizonPoint N)) = 1 := by
  filter_upwards [eventually_hermNegIndex_atom_le_one hε, eventually_one_le_hermNegIndex_atom hε]
    with N h₁ h₂ D hD hD'
  exact le_antisymm (h₁ D hD) (h₂ D hD')

/-- **Conductor `2` is the first rung after the pole**: every conductor `m ≥ 3` has adjunction
energy above `E₂ = γ + 2 log 2`. -/
theorem ramanujanAdjunctionEnergy_two_lt {m : ℕ} (hm : 3 ≤ m) :
    ramanujanAdjunctionEnergy 2 < ramanujanAdjunctionEnergy m := by
  rw [ramanujanAdjunctionEnergy_two, ramanujanAdjunctionEnergy]
  linarith [two_mul_log_two_lt_log_add_tameDifferent hm]

/-- **Every adjunction energy is a rung of the index ladder.** For a finite set `M` of conductors
with `2δ`-separated adjunction energies, eventually in `N`, the atomic kernel has at least `|M|`
negative squares once `D < log N − E_m − δ` for every `m ∈ M`. -/
theorem eventually_card_le_hermNegIndex_atom {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' →
      2 * δ ≤ |ramanujanAdjunctionEnergy m - ramanujanAdjunctionEnergy m'|) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, (∀ m ∈ M, D < Real.log N - ramanujanAdjunctionEnergy m - δ) →
      M.card ≤ hermNegIndex (gram (atomKernel D) (horizonPoint N)) := by
  have hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ M, ∃ i : PrimeHorizonIndex N,
      |(fullPrimeMatrix_isHermitian N).eigenvalues i - (Real.log N - ramanujanAdjunctionEnergy m)| <
        δ :=
    (eventually_all_finset M).mpr fun m hm => eventually_fullPrimeMatrix_eigenvalue_near (hM m hm) hδ
  filter_upwards [hev] with N hN D hD
  choose s hs using hN
  set t : Fin M.card → PrimeHorizonIndex N := fun i => s _ (M.equivFin.symm i).2
  have ht : Function.Injective t := by
    intro i j hij
    by_contra hne
    have hne' : (M.equivFin.symm i : ℕ) ≠ M.equivFin.symm j := fun h =>
      hne (M.equivFin.symm.injective (Subtype.ext h))
    have h1 := hs _ (M.equivFin.symm i).2
    have h2 := hs _ (M.equivFin.symm j).2
    change s _ (M.equivFin.symm i).2 = s _ (M.equivFin.symm j).2 at hij
    rw [hij] at h1
    have h3 := hsep _ (M.equivFin.symm i).2 _ (M.equivFin.symm j).2 hne'
    obtain ⟨a1, a2⟩ := abs_lt.mp h1
    obtain ⟨b1, b2⟩ := abs_lt.mp h2
    rcases abs_cases (ramanujanAdjunctionEnergy (M.equivFin.symm i) -
      ramanujanAdjunctionEnergy (M.equivFin.symm j)) with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  exact le_hermNegIndex_atom_of_eigen ht fun i => by
    have h1 := (abs_lt.mp (hs _ (M.equivFin.symm i).2)).1
    have h2 := hD _ (M.equivFin.symm i).2
    linarith

/-! ### Twins: the same index, a different carrier -/

/-- The atomic matrix of a gauge `ω`: `D·1 − (ω_m ω_n P(m, n))`. -/
def gaugeAtomMatrix (N : ℕ) (D : ℝ) (ω : ℕ → ℝ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun m n => ω m * atomMatrix N D m n * ω n

theorem hermQuad_gaugeAtomMatrix (N : ℕ) (D : ℝ) (ω : ℕ → ℝ) (c : PrimeHorizonIndex N → ℂ) :
    hermQuad ((gaugeAtomMatrix N D ω).map (↑)) c =
      hermQuad ((atomMatrix N D).map (↑)) (fun n => (ω n : ℂ) * c n) := by
  simp only [hermQuad, dotProduct, mulVec, Matrix.map_apply, gaugeAtomMatrix, Pi.star_apply,
    star_mul', RCLike.star_def, conj_ofReal, mul_sum]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- **The index is twin-blind.** Every sign gauge has the atomic index ladder of `ζ`. -/
theorem hermNegIndex_gaugeAtom_eq (N : ℕ) (D : ℝ) {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) :
    hermNegIndex ((gaugeAtomMatrix N D ω).map (↑)) =
      hermNegIndex (gram (atomKernel D) (horizonPoint N)) := by
  rw [gram_atomKernel]
  set S := Matrix.mulVecLin (diagonal fun n : PrimeHorizonIndex N => (ω n : ℂ))
  have hS : ∀ c, S c = fun n : PrimeHorizonIndex N => (ω n : ℂ) * c n := fun c => funext fun n => by
    simp [S, Matrix.mulVec_diagonal]
  have hSS : ∀ c, S (S c) = c := fun c => funext fun n => by
    rw [hS, hS]
    simp only
    rw [← mul_assoc, ← ofReal_mul, hω, ofReal_one, one_mul]
  refine le_antisymm (hermNegIndex_le_of_hermQuad_eq _ _ S fun c => ?_)
    (hermNegIndex_le_of_hermQuad_eq _ _ S fun c => ?_)
  · rw [hermQuad_gaugeAtomMatrix, hS]
  · rw [hermQuad_gaugeAtomMatrix, ← hS, hSS]

/-- The real form of a gauge on a vector restricted from `ℕ`. -/
theorem hermQuad_gaugeAtom_restrict (N : ℕ) (D : ℝ) {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (x : ℕ → ℝ) :
    hermQuad ((gaugeAtomMatrix N D ω).map (↑)) (fun n : PrimeHorizonIndex N => (x n : ℂ)) =
      D * ∑ n ∈ Icc 1 N, x n ^ 2 - atomicWeilForm N (fun n => ω n * x n) := by
  rw [hermQuad_gaugeAtomMatrix, show (fun n : PrimeHorizonIndex N => (ω n : ℂ) * (x n : ℂ)) =
    fun n : PrimeHorizonIndex N => ((ω n * x n : ℝ) : ℂ) from funext fun n => by push_cast; ring,
    hermQuad_map_ofReal_real, atomQuad_eq]
  have hext : ∀ n ∈ Icc 1 N, horizonExtend (fun i : PrimeHorizonIndex N => ω i * x i) n =
      ω n * x n := fun n hn => by simp [horizonExtend, hn]
  congr 1
  · congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [hext n hn, mul_pow, sq (ω n), hω, one_mul]
  · unfold atomicWeilForm
    exact sum_congr rfl fun m hm => sum_congr rfl fun n hn => by rw [hext m hm, hext n hn]

theorem poleFunctional_restrict (N : ℕ) (x : ℕ → ℝ) :
    poleFunctional N (fun n : PrimeHorizonIndex N => (x n : ℂ)) =
      ((∑ n ∈ Icc 1 N, x n / Real.sqrt n : ℝ) : ℂ) := by
  simp only [poleFunctional, LinearMap.coe_mk, AddHom.coe_mk, ← ofReal_mul, ← ofReal_sum]
  congr 1
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  simp only [div_eq_mul_inv]

/-- **No sign gauge carries the index on the pole below `log N − γ − 2 log 2`.** So `ζ`'s window
is the widest: the margin of every sign gauge is at most `2 log 2`. -/
theorem eventually_exists_neg_on_pole_gauge {ε : ℝ} (hε : 0 < ε) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - 2 * Real.log 2 - ε →
      ∃ c, poleFunctional N c = 0 ∧ hermQuad ((gaugeAtomMatrix N D ω).map (↑)) c < 0 := by
  filter_upwards [eventually_forall_exists_orthogonal_atomicWeilForm_ge hε] with N h D hD
  obtain ⟨y, hy, hmass, hge⟩ := h fun n => ω n / Real.sqrt n
  refine ⟨fun n : PrimeHorizonIndex N => ((ω n * y n : ℝ) : ℂ), ?_, ?_⟩
  · have hp := poleFunctional_restrict N fun n => ω n * y n
    rw [hp, show ∑ n ∈ Icc 1 N, ω n * y n / Real.sqrt n = ∑ n ∈ Icc 1 N, y n * (ω n / Real.sqrt n) from
      sum_congr rfl fun n _ => by ring, hy, ofReal_zero]
  · have hq := hermQuad_gaugeAtom_restrict N D hω fun n => ω n * y n
    rw [hq]
    have hωω : (fun n => ω n * (ω n * y n)) = y := funext fun n => by rw [← mul_assoc, hω, one_mul]
    have hsq : ∑ n ∈ Icc 1 N, (ω n * y n) ^ 2 = ∑ n ∈ Icc 1 N, y n ^ 2 :=
      sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
    rw [hωω, hsq]
    nlinarith

/-- **The Liouville twin never carries its index on the pole below the Robin–Euler point.** -/
theorem eventually_exists_neg_on_pole_liouville {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - ε →
      ∃ c, poleFunctional N c = 0 ∧
        hermQuad ((gaugeAtomMatrix N D liouvilleSign).map (↑)) c < 0 := by
  obtain ⟨g, -, h⟩ := exists_pole_hyperplane_separates_liouville
  obtain ⟨N₀, hN₀⟩ := h ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN D hD
  obtain ⟨-, x, hx, hmass, hge⟩ := hN₀ N hN
  refine ⟨fun n : PrimeHorizonIndex N => (x n : ℂ), ?_, ?_⟩
  · rw [poleFunctional_restrict, hx, ofReal_zero]
  · rw [hermQuad_gaugeAtom_restrict N D liouvilleSign_mul_self]
    nlinarith

/-! ### Infinite index on the lattice -/

/-- Translates of the horizon by distinct primes beyond it are orthogonal for the atomic kernel. -/
theorem atomKernel_translate_eq_zero (D : ℝ) {N q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hqN : N < q) (hq'N : N < q') (hne : q ≠ q') (n j : PrimeHorizonIndex N) :
    atomKernel D ((⟨(q : ℚ), by exact_mod_cast hq.pos⟩ * horizonPoint N n)⁻¹ *
      (⟨(q' : ℚ), by exact_mod_cast hq'.pos⟩ * horizonPoint N j)) = 0 := by
  have hn := mem_Icc.mp n.2
  have hj := mem_Icc.mp j.2
  have hnd : ¬ q ∣ (j : ℕ) := fun h => by have := Nat.le_of_dvd hj.1 h; omega
  have hjd : ¬ q' ∣ (n : ℕ) := fun h => by have := Nat.le_of_dvd hn.1 h; omega
  have h₁ : ¬ q * (n : ℕ) ∣ q' * j := fun h => by
    rcases (Nat.Prime.dvd_mul hq).mp (dvd_of_mul_right_dvd h) with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hq hq').mp h)
    · exact hnd h
  have h₂ : ¬ q' * (j : ℕ) ∣ q * n := fun h => by
    rcases (Nat.Prime.dvd_mul hq').mp (dvd_of_mul_right_dvd h) with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hq' hq).mp h).symm
    · exact hjd h
  have hne' : q * (n : ℕ) ≠ q' * j := fun h => h₁ (h ▸ dvd_rfl)
  rw [atomKernel_eq D (Nat.mul_pos hq.pos hn.1) (Nat.mul_pos hq'.pos hj.1)
    (by show ((q : ℚ) * ((n : ℕ) : ℚ))⁻¹ * ((q' : ℚ) * ((j : ℕ) : ℚ)) = _
        push_cast; rw [inv_mul_eq_div]), if_neg hne', weilPrimeKernel_eq_zero h₁ h₂]
  simp

/-- **The atomic kernel has infinite index on `ℚ_{>0}` at every counterterm.** No fixed diagonal
pays the prime kernel: the gap `2 log 2` lives on finite windows with a growing counterterm and
cannot bound the index on the lattice. -/
theorem negIndex_atomKernel_eq_top (D : ℝ) : negIndex (atomKernel D) = ⊤ := by
  obtain ⟨N, hN, hlog⟩ := ((eventually_one_le_hermNegIndex_atom one_pos).and
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (D + γ + 1))).exists
  have h1 := hN D (by simp only [Function.comp_apply] at hlog; linarith)
  obtain ⟨c, hc⟩ : ∃ c, hermQuad (gram (atomKernel D) (horizonPoint N)) c < 0 := by
    by_contra hc
    push Not at hc
    have := negIndex_le_card_of_nonneg_on_ker (gram (atomKernel D) (horizonPoint N))
      (fun i : Fin 0 => i.elim0) fun c _ => hc c
    simp at this
    omega
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  obtain ⟨t, ht, hcard⟩ := (Nat.infinite_setOf_prime.sdiff (Set.finite_Iic N)).exists_subset_card_eq m
  have hmem : ∀ q : t, (q : ℕ).Prime ∧ N < q := fun q => by
    have := ht q.2
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_Iic, not_le] at this
    exact this
  have := card_le_negIndex_of_orthogonal_translates hc
    (fun q : t => (⟨((q : ℕ) : ℚ), by exact_mod_cast (hmem q).1.pos⟩ : HeckeLattice))
    fun q q' hqq' a b => atomKernel_translate_eq_zero D (hmem q).1 (hmem q').1 (hmem q).2
      (hmem q').2 (fun h => hqq' (Subtype.ext h)) a b
  rwa [Fintype.card_coe, hcard] at this

end GaloisForLFunctions.HeckeKreinToeplitz
