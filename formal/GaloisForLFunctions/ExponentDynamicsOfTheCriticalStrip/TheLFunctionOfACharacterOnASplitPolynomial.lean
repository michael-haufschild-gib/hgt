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
* **The top coefficient** (`norm_degSumW_charW_pred`): for `χ^m ≠ 1`, `m = deg f`,
  `s_{m−1} g(χ^m) = (unit) g(χ)^m Π_α χ(d_α)` (`sum_monicDeg_pred_char_mul_gaussSum`), so
  `|s_{m−1}| = q^{(m−1)/2}`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.WeilKloosterman RHTower.Stepanov RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ)

/-- The weight `w(P) = χ(Res(P, f))`. -/
noncomputable def charW (f P : F[X]) : ℂ := χ (resultant P f)

omit [Fintype F] in
theorem charW_mul (f : F[X]) {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic) :
    charW χ f (P * Q) = charW χ f P * charW χ f Q := by
  have h := resultant_mul_left P Q f f.natDegree le_rfl
  rw [← hP.natDegree_mul hQ] at h
  unfold charW
  rw [h, map_mul]

omit [Fintype F] in
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

/-- A nonzero value of a character of a finite field has modulus one. -/
theorem norm_char_eq_one {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  have h : χ a ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  have hq : Fintype.card F - 1 ≠ 0 := by have := Fintype.one_lt_card (α := F); omega
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq).mp this

/-- `Φ(C t · u) = χ(t)^m Φ(u)`. -/
theorem prod_char_C_mul {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) (t : F) (u : F[X]) :
    ∏ α ∈ rootSet' f, χ ((C t * u).eval α) = χ t ^ f.natDegree * ∏ α ∈ rootSet' f, χ (u.eval α) := by
  simp only [eval_mul, eval_C, map_mul, Finset.prod_mul_distrib, Finset.prod_const,
    card_rootSet' hsq hsplit]

/-- **The top degree sum.** For `χ^m ≠ 1`, `m = deg f`, and
`s = Σ_{h monic, deg h = m−1} Π_α χ(h(α))`: `s · g(χ^m) = g(χ)^m Π_α χ(d_α)`,
`d_α = Π_{β ≠ α}(α − β)`. Lagrange interpolation turns the leading coefficient into
`Σ_α h(α)/d_α`, and the sum over all polynomials of degree `< m` factors over the roots. -/
theorem sum_monicDeg_pred_char_mul_gaussSum {χ : MulChar F ℂ} {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) (hχm : χ ^ f.natDegree ≠ 1) (ψ : AddChar F ℂ) :
    (∑ h ∈ monicDeg (f.natDegree - 1), ∏ α ∈ rootSet' f, χ (h.eval α)) *
        gaussSum (χ ^ f.natDegree) ψ =
      gaussSum χ ψ ^ f.natDegree * ∏ α ∈ rootSet' f, χ (∏ β ∈ (rootSet' f).erase α, (α - β)) := by
  set m := f.natDegree with hmdef
  set R := rootSet' f
  set d : F → F := fun α => ∏ β ∈ R.erase α, (α - β)
  set Φ : F[X] → ℂ := fun u => ∏ α ∈ R, χ (u.eval α)
  set τ := gaussSum χ ψ
  set S := ∑ h ∈ monicDeg (m - 1), Φ h
  have hd0 : ∀ α ∈ R, d α ≠ 0 := by
    intro α hα
    refine Finset.prod_ne_zero_iff.mpr fun β hβ => sub_ne_zero.mpr ?_
    exact (Finset.ne_of_mem_erase hβ).symm
  have way1 : ∑ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) =
      ∏ α ∈ R, (χ (d α) * τ) := by
    have step : ∀ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) =
        ∏ α : R, (χ (ev f c α) * ψ ((d α)⁻¹ * ev f c α)) := by
      intro c
      rw [coeff_pred_eq_sum hsq hsplit (ofCoeffs_natDegree_lt hm c), addChar_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort R]
      refine Finset.prod_congr rfl fun α _ => ?_
      simp only [ev, div_eq_inv_mul]
      rfl
    rw [Finset.sum_congr rfl fun c _ => step c,
      sum_ev hsq hsplit (fun v => ∏ α : R, (χ (v α) * ψ ((d α)⁻¹ * v α))),
      ← Fintype.prod_sum (fun (α : R) (y : F) => χ y * ψ ((d α)⁻¹ * y)),
      ← Finset.prod_coe_sort R (fun α => χ (d α) * τ)]
    refine Finset.prod_congr rfl fun α _ => ?_
    have h := gaussSum_mulShift_eq χ ψ (Units.mk0 _ (inv_ne_zero (hd0 α α.2)))
    simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at h
    rw [h, MulChar.inv_apply', inv_inv]
    rfl
  have hfib : ∀ t : F, t ≠ 0 →
      ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = t), Φ (ofCoeffs c) =
        χ t ^ m * S := by
    intro t ht
    rw [show S = ∑ h ∈ monicDeg (m - 1), Φ h from rfl, Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun h => fun i : Fin m => (C t * h).coeff i)
      (fun c => C t⁻¹ * ofCoeffs c) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      rw [mem_monicDeg] at hh
      simp only [Finset.mem_filter, mem_univ, true_and, coeff_C_mul]
      rw [show (m - 1 : ℕ) = h.natDegree from hh.2.symm, hh.1.coeff_natDegree, mul_one]
    · intro c hc
      simp only [Finset.mem_filter, mem_univ, true_and] at hc
      rw [mem_monicDeg]
      have hlead : (ofCoeffs c).coeff (m - 1) = t := by
        rw [show (m - 1 : ℕ) = ((⟨m - 1, by omega⟩ : Fin m) : ℕ) from rfl, ofCoeffs_coeff, hc]
      have hdeg : (ofCoeffs c).natDegree = m - 1 := by
        refine le_antisymm (Nat.le_sub_one_of_lt (ofCoeffs_natDegree_lt hm c)) ?_
        exact le_natDegree_of_ne_zero (by rw [hlead]; exact ht)
      refine ⟨?_, by rw [natDegree_C_mul (inv_ne_zero ht), hdeg]⟩
      rw [Monic, leadingCoeff, natDegree_C_mul (inv_ne_zero ht), hdeg, coeff_C_mul, hlead,
        inv_mul_cancel₀ ht]
    · intro h hh
      rw [mem_monicDeg] at hh
      have hdeg : (C t * h).natDegree < m := by
        rw [natDegree_C_mul ht, hh.2]; omega
      rw [ofCoeffs_coeff_eq hdeg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ht, C_1, one_mul]
    · intro c _
      funext i
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ht, C_1, one_mul, ofCoeffs_coeff]
    · intro h hh
      simp only [Φ]
      rw [mem_monicDeg] at hh
      have hdeg : (C t * h).natDegree < m := by
        rw [natDegree_C_mul ht, hh.2]; omega
      rw [ofCoeffs_coeff_eq hdeg, prod_char_C_mul χ hsq hsplit]
  have hzero : ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = 0),
      Φ (ofCoeffs c) = 0 := by
    obtain ⟨s, hs0, hs⟩ : ∃ s : F, s ≠ 0 ∧ χ s ^ m ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hχm
      ext a
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
      exact hcon a a.ne_zero
    set Z := ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = 0), Φ (ofCoeffs c)
    have h1 : Z = ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = 0),
        Φ (ofCoeffs (s • c)) := by
      refine Finset.sum_nbij' (fun c => s⁻¹ • c) (fun c => s • c) ?_ ?_ ?_ ?_ ?_
      · intro c hc
        simp only [Finset.mem_filter, mem_univ, true_and, Pi.smul_apply, smul_eq_mul] at hc ⊢
        rw [hc, mul_zero]
      · intro c hc
        simp only [Finset.mem_filter, mem_univ, true_and, Pi.smul_apply, smul_eq_mul] at hc ⊢
        rw [hc, mul_zero]
      · intro c _; rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      · intro c _; rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      · intro c _; rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    have h2 : ∀ c : Fin m → F, Φ (ofCoeffs (s • c)) = χ s ^ m * Φ (ofCoeffs c) := by
      intro c
      simp only [Φ]
      rw [ofCoeffs_smul, prod_char_C_mul χ hsq hsplit]
    have hZ : Z = χ s ^ m * Z := by
      conv_lhs => rw [h1]
      rw [Finset.sum_congr rfl fun c _ => h2 c, ← Finset.mul_sum]
    have : (1 - χ s ^ m) * Z = 0 := by linear_combination hZ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hs))
  have way2 : ∑ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) =
      S * gaussSum (χ ^ m) ψ := by
    have hco : ∀ c : Fin m → F, (ofCoeffs c).coeff (m - 1) = c ⟨m - 1, by omega⟩ :=
      fun c => ofCoeffs_coeff c ⟨m - 1, by omega⟩
    simp_rw [hco]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin m → F => c ⟨m - 1, by omega⟩)
      (t := univ) (fun _ _ => mem_univ _)]
    have : ∀ t : F, ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = t),
        Φ (ofCoeffs c) * ψ (c ⟨m - 1, by omega⟩) = (χ ^ m) t * ψ t * S := by
      intro t
      rw [Finset.sum_congr rfl fun c hc => by
        rw [(Finset.mem_filter.mp hc).2], ← Finset.sum_mul, MulChar.pow_apply' χ hm.ne']
      by_cases ht : t = 0
      · rw [ht, hzero, MulChar.map_zero, zero_pow hm.ne']; ring
      · rw [hfib t ht]; ring
    rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.sum_mul]
    simp only [gaussSum]
    ring
  rw [← way2, way1, Finset.prod_mul_distrib, Finset.prod_const, card_rootSet' hsq hsplit]
  ring

/-- **The functional equation of the top coefficient**: for `χ ≠ 1` and `χ^m ≠ 1`,
`|s_{m−1}| = q^{(m−1)/2}`. -/
theorem norm_degSumW_charW_pred {χ : MulChar F ℂ} (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) (hχm : χ ^ f.natDegree ≠ 1) :
    ‖degSumW (charW χ f) (f.natDegree - 1)‖ = Real.sqrt (Fintype.card F) ^ (f.natDegree - 1) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hm
  have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have key := sum_monicDeg_pred_char_mul_gaussSum hsq hsplit hm hχm ψ
  have hg1 := ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card hχ hψ
  have hgm := ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card hχm hψ
  have hd : ‖∏ α ∈ rootSet' f, χ (∏ β ∈ (rootSet' f).erase α, (α - β))‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun α _ => norm_char_eq_one χ ?_
    refine Finset.prod_ne_zero_iff.mpr fun β hβ => sub_ne_zero.mpr ?_
    exact (Finset.ne_of_mem_erase hβ).symm
  have hS := congrArg norm key
  rw [norm_mul, norm_mul, norm_pow, hg1, hgm, hd, mul_one] at hS
  have hsq0 : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hS' : ‖∑ h ∈ monicDeg (f.natDegree - 1), ∏ α ∈ rootSet' f, χ (h.eval α)‖ =
      Real.sqrt (Fintype.card F) ^ (f.natDegree - 1) := by
    have hm1 : f.natDegree = (f.natDegree - 1) + 1 := by omega
    rw [hm1, pow_succ] at hS
    exact mul_right_cancel₀ hsq0.ne' hS
  unfold degSumW
  rw [Finset.sum_congr rfl fun h hh => by rw [charW_eq_prod χ hsq hsplit, (mem_monicDeg.mp hh).2],
    ← Finset.mul_sum, norm_mul, hS',
    norm_char_eq_one χ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hc0)),
    one_mul]

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
