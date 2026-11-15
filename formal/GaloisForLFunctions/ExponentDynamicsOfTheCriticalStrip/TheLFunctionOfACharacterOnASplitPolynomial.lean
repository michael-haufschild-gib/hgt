import GaloisForLFunctions.RHTower.HyperellipticDegreeSums

/-!
# The L-function of a character on a split polynomial

For a multiplicative character `χ : F → ℂ` of a finite field and `f ∈ F[X]`, the weight
`w(P) = χ(Res(P, f))` (`charW`) is multiplicative on monic polynomials (`charW_mul`), and:

* **Extensions** (`extChar_eq_powerSumW`): `Σ_{x ∈ E} χ(N_{E/F} f(x)) = c_n`, `n = [E : F]`, the power
  sum of the weight; `N_{E/F}(f(x)) = Res(minpoly x, f)^{n/d}` and the points of `E` fall into the
  fibres of the minimal polynomial.
* **The weight on the roots** (`charW_eq_prod`): for `f` split and squarefree,
  `w(h) = χ((−1)^{km} c^k) Π_{α} χ(h(α))`.
* **Vanishing** (`degSumW_charW_eq_zero`): for `χ ≠ 1` the degree sums `s_k` vanish for `k ≥ deg f`:
  translating `h` by every polynomial of degree `< deg f` makes its values on the roots uniform, and
  `Σ_t χ(t) = 0`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.WeilKloosterman RHTower.Stepanov RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ)

/-- The weight `w(P) = χ(Res(P, f))`. -/
noncomputable def charW (f P : F[X]) : ℂ := χ (resultant P f)

theorem charW_mul (f : F[X]) {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic) :
    charW χ f (P * Q) = charW χ f P * charW χ f Q := by
  have h := resultant_mul_left P Q f f.natDegree le_rfl
  rw [← hP.natDegree_mul hQ] at h
  unfold charW
  rw [h, map_mul]

theorem charW_one (f : F[X]) : charW χ f 1 = 1 := by
  unfold charW
  rw [show resultant (1 : F[X]) f = 1 by
    rw [← C_1, resultant, natDegree_C]
    simp]
  exact map_one χ

variable {E : Type*} [Field E] [Fintype E] [Algebra F E]

/-- The character sum `Σ_{x ∈ E} χ(N_{E/F} f(x))` over a finite extension. -/
noncomputable def extChar (f : F[X]) : ℂ := ∑ x : E, χ (Algebra.norm F (aeval x f))

theorem char_norm_aeval_eq (f : F[X]) (x : E) :
    χ (Algebra.norm F (aeval x f)) =
      charW χ f (minpoly F x) ^ (Module.finrank F E / (minpoly F x).natDegree) := by
  rw [norm_aeval_eq_resultant_pow, map_pow]
  rfl

/-- **The extension sums are the power sums of the weight.** -/
theorem extChar_eq_powerSumW (f : F[X]) :
    extChar χ (E := E) f = powerSumW (charW χ f) (Module.finrank F E) := by
  set n := Module.finrank F E
  have hn : 0 < n := Module.finrank_pos
  unfold extChar
  simp_rw [char_norm_aeval_eq χ f]
  set t : Finset F[X] := n.divisors.biUnion (irrDeg (F := F))
  have hmaps : ∀ x ∈ (univ : Finset E), minpoly F x ∈ t := by
    intro x _
    have hi : IsIntegral F x := IsIntegral.of_finite F x
    rw [Finset.mem_biUnion]
    refine ⟨(minpoly F x).natDegree, ?_,
      mem_irrDeg.mpr ⟨minpoly.monic hi, rfl, minpoly.irreducible hi⟩⟩
    rw [Nat.mem_divisors]
    exact ⟨minpoly.degree_dvd hi, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ P ∈ t, (∑ x ∈ univ.filter (fun x : E => minpoly F x = P),
      charW χ f (minpoly F x) ^ (n / (minpoly F x).natDegree)) =
      (P.natDegree : ℂ) * charW χ f P ^ (n / P.natDegree) := by
    intro P hP
    rw [Finset.mem_biUnion] at hP
    obtain ⟨d, hd, hPd⟩ := hP
    rw [mem_irrDeg] at hPd
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, card_minpoly_fiber hPd.1 hPd.2.2, hPd.2.1,
      if_pos (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfib, Finset.sum_biUnion]
  · unfold powerSumW
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun P hP => ?_))
    rw [(mem_irrDeg.mp hP).2.1]
  · intro d _ e _ hde
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hPd hPe
    rw [mem_irrDeg] at hPd hPe
    exact hde (hPd.2.1.symm.trans hPe.2.1)

/-- **The weight on the roots.** -/
theorem charW_eq_prod {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) (h : F[X]) :
    charW χ f h = χ ((-1) ^ (h.natDegree * f.natDegree) * f.leadingCoeff ^ h.natDegree) *
      ∏ α ∈ rootSet' f, χ (h.eval α) := by
  rw [charW, resultant_comm, resultant_eq_prod_eval f h h.natDegree le_rfl hsplit,
    map_mul, map_mul, map_mul, ← mul_assoc, map_multiset_prod, Multiset.map_map,
    prod_roots_eq_prod_rootSet' hsq]
  rfl

/-- `Σ_t χ(b + t) = 0` for `χ ≠ 1`. -/
theorem sum_char_add {χ : MulChar F ℂ} (hχ : χ ≠ 1) (b : F) : ∑ t : F, χ (b + t) = 0 := by
  rw [Fintype.sum_equiv (Equiv.addLeft b) (fun t => χ (b + t)) (fun t => χ t) (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- **Vanishing**: for `χ ≠ 1` and `k ≥ m ≥ 1`, `Σ_{h monic, deg h = k} Π_α χ(h(α)) = 0`. -/
theorem sum_monicDeg_prod_char_eq_zero {χ : MulChar F ℂ} (hχ : χ ≠ 1) {f : F[X]}
    (hsq : Squarefree f) (hsplit : f.Splits) (hm : 0 < f.natDegree) {k : ℕ} (hk : f.natDegree ≤ k) :
    ∑ h ∈ monicDeg k, ∏ α ∈ rootSet' f, χ (h.eval α) = 0 := by
  set m := f.natDegree
  set S := ∑ h ∈ monicDeg k, ∏ α ∈ rootSet' f, χ (h.eval α)
  have hshift : ∀ c : Fin m → F, S = ∑ h ∈ monicDeg k,
      ∏ α ∈ rootSet' f, χ (h.eval α + (ofCoeffs c).eval α) := by
    intro c
    have hu : (ofCoeffs c).natDegree < k := lt_of_lt_of_le (ofCoeffs_natDegree_lt hm c) hk
    refine Finset.sum_nbij' (fun h => h - ofCoeffs c) (fun h => h + ofCoeffs c) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      rw [mem_monicDeg] at hh ⊢
      have h1 : (h - ofCoeffs c).natDegree = k := by
        rw [natDegree_sub_eq_left_of_natDegree_lt (hh.2 ▸ hu)]; exact hh.2
      refine ⟨?_, h1⟩
      rw [Monic, leadingCoeff, h1, coeff_sub, ← hh.2, hh.1.coeff_natDegree,
        coeff_eq_zero_of_natDegree_lt (hh.2 ▸ hu), sub_zero]
    · intro h hh
      rw [mem_monicDeg] at hh ⊢
      have h1 : (h + ofCoeffs c).natDegree = k := by
        rw [natDegree_add_eq_left_of_natDegree_lt (hh.2 ▸ hu)]; exact hh.2
      refine ⟨?_, h1⟩
      rw [Monic, leadingCoeff, h1, coeff_add, ← hh.2, hh.1.coeff_natDegree,
        coeff_eq_zero_of_natDegree_lt (hh.2 ▸ hu), add_zero]
    · intro h _; ring
    · intro h _; ring
    · intro h _
      refine Finset.prod_congr rfl fun α _ => ?_
      rw [eval_sub, sub_add_cancel]
  have hsum : (Fintype.card F : ℂ) ^ m * S = 0 := by
    have hcard : (Fintype.card F : ℂ) ^ m = ∑ _c : Fin m → F, (1 : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; simp
    rw [hcard, Finset.sum_mul, Finset.sum_congr rfl fun c _ => by rw [one_mul, hshift c],
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun h _ => ?_
    have := sum_ev hsq hsplit (fun v => ∏ α ∈ (univ : Finset (rootSet' f)),
      χ (h.eval (α : F) + v α))
    simp only [ev] at this
    rw [show (∑ c : Fin m → F, ∏ α ∈ rootSet' f, χ (h.eval α + (ofCoeffs c).eval α)) =
        ∑ c : Fin m → F, ∏ α ∈ (univ : Finset (rootSet' f)),
          χ (h.eval (α : F) + (ofCoeffs c).eval (α : F)) by
      refine Finset.sum_congr rfl fun c _ => ?_
      exact (Finset.prod_coe_sort (rootSet' f) _).symm]
    rw [this, ← Fintype.prod_sum (fun (α : rootSet' f) (y : F) => χ (h.eval (α : F) + y))]
    obtain ⟨α0, hα0⟩ : (rootSet' f).Nonempty := by
      rw [← Finset.card_pos, card_rootSet' hsq hsplit]; exact hm
    exact Finset.prod_eq_zero (mem_univ ⟨α0, hα0⟩) (sum_char_add hχ _)
  have hq : (Fintype.card F : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  exact (mul_eq_zero.mp hsum).resolve_left hq

/-- **The L-function is a polynomial of degree `< m`**: `s_k = 0` for `k ≥ m`. -/
theorem degSumW_charW_eq_zero {χ : MulChar F ℂ} (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) {k : ℕ} (hk : f.natDegree ≤ k) :
    degSumW (charW χ f) k = 0 := by
  unfold degSumW
  rw [Finset.sum_congr rfl fun h hh => by rw [charW_eq_prod χ hsq hsplit, (mem_monicDeg.mp hh).2]]
  rw [← Finset.mul_sum, sum_monicDeg_prod_char_eq_zero hχ hsq hsplit hm hk, mul_zero]

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
