import GaloisForLFunctions.RHTower.HyperellipticLFunction
import GaloisForLFunctions.RHTower.StepanovCount
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheTorsionCharacteristics

/-!
# The degree sums of a split hyperelliptic L-function

Let `f = c Π_{α ∈ R} (X − α)` be squarefree and split over `F`, `m = deg f = |R|`, and
`s_k = Σ_{h monic, deg h = k} χ(Res(h, f))` the degree sums of the weight `w`.

* **The weight on the roots** (`hypW_eq_prod`): `w(h) = χ((−1)^{km} c^k) Π_{α ∈ R} χ(h(α))`.
* **Evaluation is a bijection** (`ev_bijective`): polynomials of degree `< m` are determined by,
  and realize every vector of, their values on `R`.
* **Vanishing** (`degSumW_eq_zero`): for `k ≥ m`, translating `h` by every `u` of degree `< m`
  makes the values on `R` uniform, and `Σ_t χ(t) = 0`; so `s_k = 0` and the L-function
  `Σ_k s_k T^k` is a polynomial of degree `< m`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Hyperelliptic

open WeilKloosterman Stepanov

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- The quadratic character with complex values. -/
noncomputable def chiC (F : Type*) [Field F] [Fintype F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem chiC_apply (a : F) : chiC F a = ((quadraticChar F a : ℤ) : ℂ) := rfl

theorem hypW_eq_chiC (f P : F[X]) : hypW f P = chiC F (resultant P f) := rfl

/-- The roots of a squarefree split polynomial, as a finset of size `deg f`. -/
noncomputable def rootSet' (f : F[X]) : Finset F := f.roots.toFinset

theorem roots_nodup {f : F[X]} (hsq : Squarefree f) : f.roots.Nodup :=
  nodup_roots (PerfectField.separable_iff_squarefree.mpr hsq)

theorem card_rootSet' {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) :
    (rootSet' f).card = f.natDegree := by
  rw [rootSet', Multiset.toFinset_card_of_nodup (roots_nodup hsq), ← splits_iff_card_roots.mp hsplit]

theorem prod_roots_eq_prod_rootSet' {f : F[X]} (hsq : Squarefree f) {M : Type*} [CommMonoid M]
    (g : F → M) : (f.roots.map g).prod = ∏ α ∈ rootSet' f, g α := by
  rw [rootSet', Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (roots_nodup hsq)]

/-- **The weight on the roots**: `w(h) = χ((−1)^{km} c^k) Π_{α ∈ R} χ(h(α))`. -/
theorem hypW_eq_prod {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) (h : F[X]) :
    hypW f h = chiC F ((-1) ^ (h.natDegree * f.natDegree) * f.leadingCoeff ^ h.natDegree) *
      ∏ α ∈ rootSet' f, chiC F (h.eval α) := by
  rw [hypW_eq_chiC, resultant_comm, resultant_eq_prod_eval f h h.natDegree le_rfl hsplit,
    map_mul, map_mul, map_mul, ← mul_assoc, map_multiset_prod, Multiset.map_map,
    prod_roots_eq_prod_rootSet' hsq]
  rfl

/-! ### Evaluation on the roots -/

/-- Values on `R` of the polynomial with coefficient vector `c`. -/
noncomputable def ev (f : F[X]) {m : ℕ} (c : Fin m → F) : rootSet' f → F :=
  fun α => (ofCoeffs c).eval (α : F)

theorem ev_injective {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) :
    Function.Injective (ev f (m := f.natDegree)) := by
  intro c d hcd
  have hm : 0 < f.natDegree ∨ f.natDegree = 0 := by omega
  rcases hm with hm | hm
  · have hsub : ofCoeffs (c + (-1 : F) • d) = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
        (f := fun α : rootSet' f => (α : F)) Subtype.val_injective
      · intro α
        rw [ofCoeffs_linear, eval_add, eval_mul, eval_C]
        have := congrFun hcd α
        simp only [ev] at this
        rw [this]; ring
      · rw [Fintype.card_coe, card_rootSet' hsq hsplit]
        exact ofCoeffs_natDegree_lt hm _
    have := ofCoeffs_eq_zero hsub
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    linear_combination hi
  · funext i; exact absurd i.2 (by omega)

theorem ev_bijective {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) :
    Function.Bijective (ev f (m := f.natDegree)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨ev_injective hsq hsplit, ?_⟩
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_rootSet' hsq hsplit]

/-- `Σ_{c} G(ev c) = Σ_{v : R → F} G(v)`. -/
theorem sum_ev {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) {M : Type*} [AddCommMonoid M]
    (G : (rootSet' f → F) → M) :
    ∑ c : Fin f.natDegree → F, G (ev f c) = ∑ v : rootSet' f → F, G v :=
  Fintype.sum_bijective _ (ev_bijective hsq hsplit) _ _ fun _ => rfl

/-! ### Vanishing of the degree sums -/

/-- `Σ_t χ(b + t) = 0`. -/
theorem sum_chiC_add (hF : ringChar F ≠ 2) (b : F) : ∑ t : F, chiC F (b + t) = 0 := by
  rw [Fintype.sum_equiv (Equiv.addLeft b) (fun t => chiC F (b + t)) (fun t => chiC F t)
    (fun _ => rfl)]
  simp only [chiC_apply]
  rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]

/-- **Vanishing**: for `k ≥ m ≥ 1`, `Σ_{h monic, deg h = k} Π_{α ∈ R} χ(h(α)) = 0`. -/
theorem sum_monicDeg_prod_eq_zero (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) {k : ℕ} (hk : f.natDegree ≤ k) :
    ∑ h ∈ monicDeg k, ∏ α ∈ rootSet' f, chiC F (h.eval α) = 0 := by
  set m := f.natDegree
  set S := ∑ h ∈ monicDeg k, ∏ α ∈ rootSet' f, chiC F (h.eval α)
  -- translation by `u = ofCoeffs c` permutes the monic polynomials of degree `k`
  have hshift : ∀ c : Fin m → F, S = ∑ h ∈ monicDeg k,
      ∏ α ∈ rootSet' f, chiC F (h.eval α + (ofCoeffs c).eval α) := by
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
  -- average over all translations
  have hsum : (Fintype.card F : ℂ) ^ m * S = 0 := by
    have hcard : (Fintype.card F : ℂ) ^ m = ∑ _c : Fin m → F, (1 : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; simp
    rw [hcard, Finset.sum_mul, Finset.sum_congr rfl fun c _ => by rw [one_mul, hshift c],
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun h _ => ?_
    have := sum_ev hsq hsplit (fun v => ∏ α ∈ (univ : Finset (rootSet' f)),
      chiC F (h.eval (α : F) + v α))
    simp only [ev] at this
    rw [show (∑ c : Fin m → F, ∏ α ∈ rootSet' f, chiC F (h.eval α + (ofCoeffs c).eval α)) =
        ∑ c : Fin m → F, ∏ α ∈ (univ : Finset (rootSet' f)),
          chiC F (h.eval (α : F) + (ofCoeffs c).eval (α : F)) by
      refine Finset.sum_congr rfl fun c _ => ?_
      exact (Finset.prod_coe_sort (rootSet' f) _).symm]
    rw [this, ← Fintype.prod_sum (fun (α : rootSet' f) (y : F) => chiC F (h.eval (α : F) + y))]
    obtain ⟨α0, hα0⟩ : (rootSet' f).Nonempty := by
      rw [← Finset.card_pos, card_rootSet' hsq hsplit]; exact hm
    exact Finset.prod_eq_zero (mem_univ ⟨α0, hα0⟩) (sum_chiC_add hF _)
  have hq : (Fintype.card F : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  exact (mul_eq_zero.mp hsum).resolve_left hq

/-- **The L-function is a polynomial of degree `< m`**: `s_k = 0` for `k ≥ m`. -/
theorem degSumW_eq_zero (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) {k : ℕ} (hk : f.natDegree ≤ k) : degSumW (hypW f) k = 0 := by
  unfold degSumW
  rw [Finset.sum_congr rfl fun h hh => by
    rw [hypW_eq_prod hsq hsplit, (mem_monicDeg.mp hh).2]]
  rw [← Finset.mul_sum, sum_monicDeg_prod_eq_zero hF hsq hsplit hm hk, mul_zero]

/-! ### The leading coefficient -/

omit [Fintype F] in
theorem addChar_sum {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (a : ι → F) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem chiC_sq {a : F} (ha : a ≠ 0) : chiC F a ^ 2 = 1 := by
  rw [chiC_apply, ← Int.cast_pow, quadraticChar_sq_one ha, Int.cast_one]

theorem chiC_inv {a : F} (ha : a ≠ 0) : chiC F a⁻¹ = chiC F a := by
  have h1 : chiC F a * chiC F a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h2 := chiC_sq ha
  linear_combination (chiC F a) * h1 - (chiC F a⁻¹) * h2

theorem chiC_pow_odd {a : F} (ha : a ≠ 0) {m : ℕ} (hm : Odd m) :
    chiC F a ^ m = chiC F a := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, chiC_sq ha, one_pow, one_mul]

/-- `Σ_y χ(y) ψ(a y) = χ(a) τ` for `a ≠ 0`. -/
theorem gaussSum_mulShift_eq (ψ : AddChar F ℂ) {a : F} (ha : a ≠ 0) :
    gaussSum (chiC F) (ψ.mulShift a) = chiC F a * gaussSum (chiC F) ψ := by
  have h := gaussSum_mulShift (chiC F) ψ (Units.mk0 a ha)
  simp only [Units.val_mk0] at h
  have h2 := chiC_sq ha
  linear_combination (chiC F a) * h - gaussSum (chiC F) (ψ.mulShift a) * h2

/-- The values on the roots of a polynomial of degree `< m` determine its coefficient of `X^{m−1}`
(Lagrange): `u_{m−1} = Σ_{α ∈ R} u(α)/d_α`, `d_α = Π_{β ≠ α} (α − β)`. -/
theorem coeff_pred_eq_sum {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) {u : F[X]}
    (hu : u.natDegree < f.natDegree) :
    u.coeff (f.natDegree - 1) =
      ∑ α ∈ rootSet' f, u.eval α / ∏ β ∈ (rootSet' f).erase α, (α - β) := by
  have h := Lagrange.coeff_eq_sum (s := rootSet' f) (v := id) (Set.injOn_id _) (P := u)
    (by
      rw [card_rootSet' hsq hsplit]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast hu))
  rw [card_rootSet' hsq hsplit] at h
  simpa using h

omit [Fintype F] in
/-- `ofCoeffs` of the coefficient vector of a polynomial of degree `< m`. -/
theorem ofCoeffs_coeff_eq {m : ℕ} {p : F[X]} (hp : p.natDegree < m) :
    ofCoeffs (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases Nat.lt_or_ge n m with hn | hn
  · exact ofCoeffs_coeff (fun i : Fin m => p.coeff i) ⟨n, hn⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (ofCoeffs_natDegree_lt
      (lt_of_le_of_lt (Nat.zero_le _) hp) _) hn), coeff_eq_zero_of_natDegree_lt (by omega)]

omit [Fintype F] in
theorem ofCoeffs_smul {m : ℕ} (s : F) (c : Fin m → F) : ofCoeffs (s • c) = C s * ofCoeffs c := by
  have h := ofCoeffs_linear (0 : Fin m → F) c s
  rw [zero_add] at h
  rw [h, show ofCoeffs (0 : Fin m → F) = 0 by simp [ofCoeffs], zero_add]

/-- `Φ(C t · u) = χ(t)^m Φ(u)`. -/
theorem prod_chiC_C_mul {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits) (t : F) (u : F[X]) :
    ∏ α ∈ rootSet' f, chiC F ((C t * u).eval α) =
      chiC F t ^ f.natDegree * ∏ α ∈ rootSet' f, chiC F (u.eval α) := by
  simp only [eval_mul, eval_C, map_mul, Finset.prod_mul_distrib, Finset.prod_const,
    card_rootSet' hsq hsplit]

/-- **The leading coefficient** (functional equation): for odd `m = deg f`,
`Σ_{h monic, deg h = m−1} Π_{α ∈ R} χ(h(α)) = τ^{m−1} Π_{α ∈ R} χ(d_α)`. -/
theorem sum_monicDeg_pred_eq (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hodd : Odd f.natDegree) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ∑ h ∈ monicDeg (f.natDegree - 1), ∏ α ∈ rootSet' f, chiC F (h.eval α) =
      gaussSum (chiC F) ψ ^ (f.natDegree - 1) *
        ∏ α ∈ rootSet' f, chiC F (∏ β ∈ (rootSet' f).erase α, (α - β)) := by
  set m := f.natDegree with hmdef
  have hm : 0 < m := hodd.pos
  set R := rootSet' f
  set d : F → F := fun α => ∏ β ∈ R.erase α, (α - β)
  set Φ : F[X] → ℂ := fun u => ∏ α ∈ R, chiC F (u.eval α)
  set τ := gaussSum (chiC F) ψ
  set S := ∑ h ∈ monicDeg (m - 1), Φ h
  have hd0 : ∀ α ∈ R, d α ≠ 0 := by
    intro α hα
    refine Finset.prod_ne_zero_iff.mpr fun β hβ => sub_ne_zero.mpr ?_
    exact (Finset.ne_of_mem_erase hβ).symm
  -- Way 1: Lagrange and Gauss sums
  have way1 : ∑ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) =
      ∏ α ∈ R, (chiC F (d α) * τ) := by
    have step : ∀ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) =
        ∏ α : R, (chiC F (ev f c α) * ψ ((d α)⁻¹ * ev f c α)) := by
      intro c
      rw [coeff_pred_eq_sum hsq hsplit (ofCoeffs_natDegree_lt hm c), addChar_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort R]
      refine Finset.prod_congr rfl fun α _ => ?_
      simp only [ev, div_eq_inv_mul]
      rfl
    rw [Finset.sum_congr rfl fun c _ => step c,
      sum_ev hsq hsplit (fun v => ∏ α : R, (chiC F (v α) * ψ ((d α)⁻¹ * v α))),
      ← Fintype.prod_sum (fun (α : R) (y : F) => chiC F y * ψ ((d α)⁻¹ * y)),
      ← Finset.prod_coe_sort R (fun α => chiC F (d α) * τ)]
    refine Finset.prod_congr rfl fun α _ => ?_
    have h := gaussSum_mulShift_eq ψ (inv_ne_zero (hd0 α α.2))
    simp only [gaussSum, AddChar.mulShift_apply] at h
    rw [h, chiC_inv (hd0 α α.2)]
    rfl
  -- Way 2: the leading coefficient fibres
  have hfib : ∀ t : F, t ≠ 0 →
      ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = t), Φ (ofCoeffs c) =
        chiC F t * S := by
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
      rw [ofCoeffs_coeff_eq hdeg, prod_chiC_C_mul hsq hsplit, chiC_pow_odd ht hodd]
  have hzero : ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = 0),
      Φ (ofCoeffs c) = 0 := by
    obtain ⟨s, hs⟩ := FiniteField.exists_nonsquare hF
    have hs0 : s ≠ 0 := fun h => hs (h ▸ ⟨0, by simp⟩)
    have hχs : chiC F s = -1 := by
      rw [chiC_apply, (quadraticChar_neg_one_iff_not_isSquare).mpr hs]; simp
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
    have h2 : ∀ c : Fin m → F, Φ (ofCoeffs (s • c)) = -Φ (ofCoeffs c) := by
      intro c
      simp only [Φ]
      rw [ofCoeffs_smul, prod_chiC_C_mul hsq hsplit, chiC_pow_odd hs0 hodd, hχs]
      ring
    have hZ : Z = -Z := by
      conv_lhs => rw [h1]
      rw [Finset.sum_congr rfl fun c _ => h2 c, Finset.sum_neg_distrib]
    linear_combination hZ / 2
  have way2 : ∑ c : Fin m → F, Φ (ofCoeffs c) * ψ ((ofCoeffs c).coeff (m - 1)) = S * τ := by
    have hco : ∀ c : Fin m → F, (ofCoeffs c).coeff (m - 1) = c ⟨m - 1, by omega⟩ :=
      fun c => ofCoeffs_coeff c ⟨m - 1, by omega⟩
    simp_rw [hco]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin m → F => c ⟨m - 1, by omega⟩)
      (t := univ) (fun _ _ => mem_univ _)]
    have : ∀ t : F, ∑ c ∈ univ.filter (fun c : Fin m → F => c ⟨m - 1, by omega⟩ = t),
        Φ (ofCoeffs c) * ψ (c ⟨m - 1, by omega⟩) = chiC F t * ψ t * S := by
      intro t
      rw [Finset.sum_congr rfl fun c hc => by
        rw [(Finset.mem_filter.mp hc).2], ← Finset.sum_mul]
      by_cases ht : t = 0
      · rw [ht, hzero]; simp [MulChar.map_zero]
      · rw [hfib t ht]; ring
    rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.sum_mul]
    simp only [τ, gaussSum]
    ring
  have hτ : τ ≠ 0 := by
    have := GaloisForLFunctions.ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card
      (χ := chiC F) (by
        intro h
        obtain ⟨s, hs⟩ := FiniteField.exists_nonsquare hF
        have h1 := congrArg (fun χ : MulChar F ℂ => χ s) h
        have hs0 : s ≠ 0 := fun h => hs (h ▸ ⟨0, by simp⟩)
        simp only [MulChar.one_apply (isUnit_iff_ne_zero.mpr hs0)] at h1
        rw [chiC_apply, (quadraticChar_neg_one_iff_not_isSquare).mpr hs] at h1
        norm_num at h1) hψ
    intro h0
    have h0' : gaussSum (chiC F) ψ = 0 := h0
    rw [h0', norm_zero] at this
    have : (0 : ℝ) < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    linarith
  have key : S * τ = τ ^ m * ∏ α ∈ R, chiC F (d α) := by
    rw [← way2, way1, Finset.prod_mul_distrib, Finset.prod_const, card_rootSet' hsq hsplit]
    ring
  have hm1 : m = (m - 1) + 1 := by omega
  apply mul_right_cancel₀ hτ
  rw [key]
  conv_lhs => rw [hm1, pow_succ]
  ring

end GaloisForLFunctions.RHTower.Hyperelliptic
