import GaloisForLFunctions.RHTower.HyperellipticDegreeSums
import GaloisForLFunctions.RHTower.WeilKloostermanBound
import GaloisForLFunctions.HTGeometry.MultisetNewton

/-!
# The Riemann hypothesis for split hyperelliptic curves, by counting

Let `f` be squarefree, split over `F`, of odd degree `m`, and `s_k` the degree sums of the weight
`w(P) = χ(Res(P, f))`. Then `s_k = 0` for `k ≥ m` and `s_0 = 1`, so the reversed L-polynomial
`L*(X) = Σ_{k<m} s_k X^{m−1−k}` is monic of degree `m − 1`; let `ω` be its roots.

* **Vieta and Newton** (`powerSumW_eq_neg_rootPowerSum`): `e_k(ω) = (−1)^k s_k`, and the corpus
  Newton identity `k s_k = Σ_j c_j s_{k−j}` for the weight, compared with Newton's identity for `ω`,
  gives `c_n = −Σ ω_i^n` for all `n ≥ 1`; `c_n` is the character sum over the degree-`n` extension.
* **The product** (`norm_prod_lRoots`): `|Π ω_i| = |s_{m−1}| = q^{(m−1)/2}` (Gauss sums).
* **The upper bound** (`norm_rootEnum_le`): over `F = 𝔽_p`, Stepanov's count on the extensions of
  degree `2k` bounds the power sums of `ω_i²` by `O(p^k)`, so `|ω_i| ≤ √p`.
* **Unitarity** (`riemannHypothesis_splitHyperelliptic`): `m − 1` factors `≤ √p` with product
  `√p^{m−1}` all equal `√p`; hence the Hasse–Weil bound
  `|#{y² = f(x)}(E) − |E|| ≤ (m − 1)√|E|` (`abs_card_points_sub_le_splitHyperelliptic`).

The only positivity is counting: Stepanov's auxiliary section and `|τ|² = q`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Hyperelliptic

open WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- The degree sums `s_k = Σ_{deg h = k} w(h)`. -/
noncomputable def degSum (f : F[X]) (k : ℕ) : ℂ := degSumW (hypW f) k

theorem degSum_zero (f : F[X]) : degSum f 0 = 1 := by
  unfold degSum degSumW
  rw [sum_monicDeg]
  simp [monicOf, hypW_one]

/-- The reversed L-polynomial `L*(X) = Σ_{k<m} s_k X^{m−1−k}`. -/
noncomputable def lPoly (f : F[X]) : ℂ[X] :=
  ∑ k ∈ range f.natDegree, C (degSum f k) * X ^ (f.natDegree - 1 - k)

theorem lPoly_coeff (f : F[X]) {j : ℕ} (hj : j < f.natDegree) :
    (lPoly f).coeff j = degSum f (f.natDegree - 1 - j) := by
  unfold lPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (f.natDegree - 1 - j)]
  · rw [if_pos (by omega)]
  · intro k hk hkj
    rw [if_neg (by have := mem_range.mp hk; omega)]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

theorem lPoly_natDegree_le (f : F[X]) : (lPoly f).natDegree ≤ f.natDegree - 1 := by
  unfold lPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem lPoly_monic (f : F[X]) (hm : 0 < f.natDegree) : (lPoly f).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one (f.natDegree - 1) (lPoly_natDegree_le f) ?_
  rw [lPoly_coeff f (by omega), show f.natDegree - 1 - (f.natDegree - 1) = 0 by omega, degSum_zero]

theorem lPoly_natDegree (f : F[X]) (hm : 0 < f.natDegree) :
    (lPoly f).natDegree = f.natDegree - 1 := by
  refine le_antisymm (lPoly_natDegree_le f) ?_
  exact le_natDegree_of_ne_zero (by
    rw [lPoly_coeff f (by omega), show f.natDegree - 1 - (f.natDegree - 1) = 0 by omega,
      degSum_zero]; exact one_ne_zero)

/-- The reciprocal roots `ω` of the L-function. -/
noncomputable def lRoots (f : F[X]) : Multiset ℂ := (lPoly f).roots

theorem card_lRoots (f : F[X]) (hm : 0 < f.natDegree) :
    Multiset.card (lRoots f) = f.natDegree - 1 := by
  rw [lRoots, IsAlgClosed.card_roots_eq_natDegree, lPoly_natDegree f hm]

/-- **Vieta**: `e_k(ω) = (−1)^k s_k`. -/
theorem esymm_lRoots (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (k : ℕ) :
    (lRoots f).esymm k = (-1) ^ k * degSum f k := by
  rcases Nat.lt_or_ge k f.natDegree with hk | hk
  · have h := coeff_eq_esymm_roots_of_card (p := lPoly f)
      (by rw [IsAlgClosed.card_roots_eq_natDegree]) (k := f.natDegree - 1 - k)
      (by rw [lPoly_natDegree f hm]; omega)
    rw [lPoly_coeff f (by omega), show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega,
      (lPoly_monic f hm).leadingCoeff, lPoly_natDegree f hm,
      show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega, one_mul] at h
    rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rfl
  · rw [show degSum f k = 0 from degSumW_eq_zero hF hsq hsplit hm hk, mul_zero, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by rw [card_lRoots f hm]; omega)]
    simp

/-- The power sums `p_n = Σ ω_i^n` of the reciprocal roots. -/
noncomputable def rootPowerSum (f : F[X]) (n : ℕ) : ℂ := ((lRoots f).map (· ^ n)).sum

/-- An enumeration of a multiset. -/
noncomputable def rootEnum (s : Multiset ℂ) : Fin s.toList.length → ℂ := fun i => s.toList.get i

theorem univ_map_rootEnum (s : Multiset ℂ) : (univ.val.map (rootEnum s)) = s := by
  rw [Fin.univ_val_map]
  unfold rootEnum
  rw [List.ofFn_get, Multiset.coe_toList]

/-- **Newton's identity for the reciprocal roots**: `n s_n = −Σ_{k<n} s_k p_{n−k}`, `n ≥ 1`. -/
theorem newton_lRoots (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) * degSum f n = -∑ k ∈ range n, degSum f k * rootPowerSum f (n - k) := by
  have hN := GaloisForLFunctions.multiset_newton (rootEnum (lRoots f)) n hn
  have hmap : ∀ j, (univ.val.map fun i => rootEnum (lRoots f) i ^ j).sum = rootPowerSum f j := by
    intro j
    rw [show (univ.val.map fun i => rootEnum (lRoots f) i ^ j) = (univ.val.map (rootEnum (lRoots f))).map (· ^ j) by
      rw [Multiset.map_map]; rfl, univ_map_rootEnum]
    rfl
  simp only [hmap] at hN
  rw [univ_map_rootEnum] at hN
  simp only [esymm_lRoots hF hsq hsplit hm] at hN
  -- rewrite the antidiagonal sum as a sum over `0 < k < n`
  have hanti : ∑ a ∈ {a ∈ antidiagonal n | a.1 ∈ Set.Ioo 0 n},
      (-1) ^ a.1 * ((-1) ^ a.1 * degSum f a.1) * rootPowerSum f a.2 =
      ∑ k ∈ range n, if 0 < k then degSum f k * rootPowerSum f (n - k) else 0 := by
    rw [Finset.sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => if a ∈ Set.Ioo 0 n then (-1) ^ a * ((-1) ^ a * degSum f a) * rootPowerSum f b
        else 0), sum_range_succ]
    simp only [Set.mem_Ioo, lt_irrefl, and_false, if_false, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn := mem_range.mp hk
    by_cases hk0 : 0 < k
    · rw [if_pos ⟨hk0, hkn⟩, if_pos hk0, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_mul]
    · rw [if_neg (fun h => hk0 h.1), if_neg hk0]
  rw [hanti] at hN
  have hsplit0 : ∑ k ∈ range n, degSum f k * rootPowerSum f (n - k) =
      rootPowerSum f n + ∑ k ∈ range n, if 0 < k then degSum f k * rootPowerSum f (n - k) else 0 := by
    rw [← Nat.succ_pred_eq_of_pos hn, sum_range_succ', sum_range_succ']
    simp only [degSum_zero, one_mul, Nat.sub_zero, lt_irrefl, if_false, add_zero,
      Nat.succ_pos, if_true]
    ring
  rw [hsplit0]
  have hsign : (-1 : ℂ) ^ (n + 1) * n * ((-1) ^ n * degSum f n) = -(n * degSum f n) := by
    rw [pow_succ]
    have : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination -(n * degSum f n) * this
  rw [hsign] at hN
  linear_combination hN

/-- **The power sums of the weight are minus the power sums of the reciprocal roots**:
`c_n = −Σ ω_i^n` for `n ≥ 1`. -/
theorem powerSumW_eq_neg_rootPowerSum (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) :
    powerSumW (hypW f) n = -rootPowerSum f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hc := newton_identity (hypW f) (fun _ _ hP hQ => hypW_mul f hP hQ) (hypW_one f) (n' + 1)
    have hr := newton_lRoots hF hsq hsplit hm hn
    change ((n' + 1 : ℕ) : ℂ) * degSum f (n' + 1) = _ at hc
    -- reindex the corpus identity over `k = n − j`
    have hre : ∑ j ∈ Finset.Icc 1 (n' + 1), powerSumW (hypW f) j * degSumW (hypW f) (n' + 1 - j) =
        ∑ k ∈ range (n' + 1), powerSumW (hypW f) (n' + 1 - k) * degSum f k := by
      refine Finset.sum_nbij' (fun j => n' + 1 - j) (fun k => n' + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [mem_range]; omega
      · intro k hk; rw [mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro j hj; rw [Finset.mem_Icc] at hj; omega
      · intro k hk; rw [mem_range] at hk; omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [show n' + 1 - (n' + 1 - j) = j by omega]
        rfl
    rw [hre, sum_range_succ'] at hc
    rw [sum_range_succ'] at hr
    simp only [Nat.sub_zero, degSum_zero, mul_one, one_mul] at hc hr
    have hih : ∀ k ∈ range n', powerSumW (hypW f) (n' + 1 - (k + 1)) * degSum f (k + 1) =
        -(degSum f (k + 1) * rootPowerSum f (n' + 1 - (k + 1))) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [ih (n' + 1 - (k + 1)) (by omega) (by omega)]
      ring
    rw [Finset.sum_congr rfl hih, Finset.sum_neg_distrib] at hc
    linear_combination hr - hc

/-! ### The product of the reciprocal roots -/

theorem prod_lRoots (f : F[X]) (hm : 0 < f.natDegree) :
    (lRoots f).prod = (-1) ^ (f.natDegree - 1) * degSum f (f.natDegree - 1) := by
  have hmon := lPoly_monic f hm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (IsAlgClosed.card_roots_eq_natDegree (p := lPoly f))
  have h0 := congrArg (eval 0) hprod
  rw [eval_multiset_prod, Multiset.map_map] at h0
  simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub] at h0
  rw [Multiset.prod_map_neg, ← coeff_zero_eq_eval_zero, lPoly_coeff f hm, Nat.sub_zero] at h0
  have hc : Multiset.card (lPoly f).roots = f.natDegree - 1 := card_lRoots f hm
  rw [hc] at h0
  have hsq : ((-1 : ℂ) ^ (f.natDegree - 1)) * (-1) ^ (f.natDegree - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  change (-1) ^ (f.natDegree - 1) * (lRoots f).prod = _ at h0
  linear_combination (-1 : ℂ) ^ (f.natDegree - 1) * h0 - (lRoots f).prod * hsq

theorem norm_chiC {a : F} (ha : a ≠ 0) : ‖chiC F a‖ = 1 := by
  rcases quadraticChar_dichotomy ha with h | h <;> simp [chiC_apply, h]

/-- **The functional equation**: `|s_{m−1}| = q^{(m−1)/2}`. -/
theorem norm_degSum_pred (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hodd : Odd f.natDegree) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖degSum f (f.natDegree - 1)‖ = Real.sqrt (Fintype.card F) ^ (f.natDegree - 1) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hodd
  have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  unfold degSum degSumW
  rw [Finset.sum_congr rfl fun h hh => by
    rw [hypW_eq_prod hsq hsplit, (mem_monicDeg.mp hh).2], ← Finset.mul_sum,
    sum_monicDeg_pred_eq hF hsq hsplit hodd ψ hψ, norm_mul, norm_mul, norm_pow,
    GaloisForLFunctions.ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card _ hψ, norm_prod,
    norm_chiC (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hc0)),
    Finset.prod_eq_one fun α hα => norm_chiC ?_]
  · ring
  · refine Finset.prod_ne_zero_iff.mpr fun β hβ => sub_ne_zero.mpr ?_
    exact (Finset.ne_of_mem_erase hβ).symm
  · intro h
    obtain ⟨s, hs⟩ := FiniteField.exists_nonsquare hF
    have hs0 : s ≠ 0 := fun h => hs (h ▸ ⟨0, by simp⟩)
    have h1 := congrArg (fun χ : MulChar F ℂ => χ s) h
    simp only [MulChar.one_apply (isUnit_iff_ne_zero.mpr hs0)] at h1
    rw [chiC_apply, (quadraticChar_neg_one_iff_not_isSquare).mpr hs] at h1
    norm_num at h1

theorem norm_prod_lRoots (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hodd : Odd f.natDegree) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖(lRoots f).prod‖ = Real.sqrt (Fintype.card F) ^ (f.natDegree - 1) := by
  rw [prod_lRoots f hodd.pos, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_degSum_pred hF hsq hsplit hodd ψ hψ]

end GaloisForLFunctions.RHTower.Hyperelliptic

/-! ### Over `𝔽_p`: the Stepanov bound on every even extension -/

namespace GaloisForLFunctions.RHTower.Hyperelliptic

open WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [hp : Fact p.Prime]

theorem ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

/-- **The Stepanov bound on the reciprocal roots**: power sums of `ω_i²` are `O(p^k)`, so
`|ω_i| ≤ √p`. -/
theorem norm_rootEnum_le (hp2 : p ≠ 2) {f : (ZMod p)[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (i : Fin (lRoots f).toList.length) :
    ‖rootEnum (lRoots f) i‖ ≤ Real.sqrt p := by
  have hF := ringChar_zmod_ne_two hp2
  set m := f.natDegree
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hbound : ∀ k, m + 5 ≤ k →
      ‖∑ j ∈ univ, (rootEnum (lRoots f) j ^ 2) ^ k‖ ≤ (3 * m + 2 : ℝ) * (p : ℝ) ^ k := by
    intro k hk
    let E := GaloisField p (2 * k)
    letI : Fintype E := Fintype.ofFinite E
    have h2k : 2 * k ≠ 0 := by omega
    have hfin : Module.finrank (ZMod p) E = 2 * k := GaloisField.finrank p h2k
    have hcard : Fintype.card E = p ^ (2 * k) := by
      rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p (2 * k) h2k
    haveI : CharP E p := charP_of_zmod
    have hl : ∑ j ∈ univ, (rootEnum (lRoots f) j ^ 2) ^ k = ((lRoots f).map (· ^ (2 * k))).sum := by
      rw [Finset.sum_eq_multiset_sum]
      conv_rhs => rw [← univ_map_rootEnum (lRoots f)]
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun j _ => ?_
      simp [← pow_mul]
    have hsum : ∑ j ∈ univ, (rootEnum (lRoots f) j ^ 2) ^ k = -extHyp (E := E) f := by
      rw [hl, extHyp_eq_powerSumW hF hsplit, hfin, powerSumW_eq_neg_rootPowerSum hF hsq hsplit hm
        (by omega), neg_neg, rootPowerSum]
    rw [hsum, norm_neg]
    -- Stepanov over `E`, `|E| = (p^k)²`
    set h := f.map (algebraMap (ZMod p) E)
    have hsep : f.Separable := PerfectField.separable_iff_squarefree.mpr hsq
    have hsqE : Squarefree h := (hsep.map).squarefree
    have hdegE : h.natDegree = m := natDegree_map _
    have hodd : Odd (p ^ (2 * k)) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨N, hN⟩ := hodd
    have hpk : m + 5 ≤ p ^ k := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left (by omega) k
      omega
    have hst := Stepanov.abs_sum_quadraticChar_le (p := p) (n := 2 * k) hcard hsqE
      (by rw [hdegE]; omega) (N := N) (s := p ^ k) (by omega) (by ring) (by rw [hdegE]; exact hpk)
    rw [hdegE] at hst
    have hext : extHyp (E := E) f = ((∑ x : E, (quadraticChar E (h.eval x) : ℤ) : ℤ) : ℂ) := by
      unfold extHyp
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [eval_map, ← aeval_def]
    rw [hext]
    set S : ℤ := ∑ x : E, (quadraticChar E (h.eval x) : ℤ)
    have hS : |(S : ℝ)| ≤ 2 * (m + 1) * (p : ℝ) ^ k + m := by exact_mod_cast hst
    have hpk1 : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
    calc ‖(S : ℂ)‖ = |(S : ℝ)| := by
          rw [show ((S : ℂ)) = ((S : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (3 * m + 2 : ℝ) * (p : ℝ) ^ k := by nlinarith
  have h := norm_le_of_power_sums_bound univ (fun j => rootEnum (lRoots f) j ^ 2)
    (C := 3 * m + 2) (ρ := p) (m0 := m + 5) (by positivity) hbound i (mem_univ i)
  rw [norm_pow] at h
  exact Real.le_sqrt_of_sq_le h

/-- If nonnegative reals `≤ c` have product `c^n` over `n` indices, each equals `c`. -/
theorem eq_of_prod_eq_pow {ι : Type*} [Fintype ι] {a : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : ∀ i, 0 ≤ a i) (hle : ∀ i, a i ≤ c) (hprod : ∏ i, a i = c ^ Fintype.card ι) :
    ∀ i, a i = c := by
  intro j
  by_contra hj
  have hlt : a j < c := lt_of_le_of_ne (hle j) hj
  have hpos : ∀ i, 0 < a i := by
    intro i
    rcases (ha i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ i, a i = 0 := Finset.prod_eq_zero (mem_univ i) h.symm
      rw [this] at hprod
      exact (pow_pos hc _).ne' hprod.symm
  have := Finset.prod_lt_prod (s := univ) (fun i _ => hpos i) (fun i _ => hle i)
    ⟨j, mem_univ j, hlt⟩
  rw [hprod, Finset.prod_const, card_univ] at this
  exact lt_irrefl _ this

/-- **The Riemann hypothesis for split odd-degree hyperelliptic curves over `𝔽_p`.**
For `p` odd and `f ∈ 𝔽_p[X]` squarefree, split, of odd degree `m`, the `m − 1` reciprocal roots of
the L-function have modulus `√p`, and for every finite extension `E` of degree `n`,
`Σ_{x ∈ E} χ_E(f(x)) = −Σ_i ω_i^n`. -/
theorem riemannHypothesis_splitHyperelliptic (hp2 : p ≠ 2) {f : (ZMod p)[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hodd : Odd f.natDegree) :
    Multiset.card (lRoots f) = f.natDegree - 1 ∧ (∀ ω ∈ lRoots f, ‖ω‖ = Real.sqrt p) ∧
      ∀ (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E],
        extHyp (E := E) f = -((lRoots f).map (· ^ Module.finrank (ZMod p) E)).sum := by
  have hF := ringChar_zmod_ne_two hp2
  have hm := hodd.pos
  refine ⟨card_lRoots f hm, ?_, ?_⟩
  · -- unitarity: each `≤ √p`, product of modulus `√p^{m−1}`
    have hprod := norm_prod_lRoots hF hsq hsplit hodd (ZMod.stdAddChar (N := p))
      (ZMod.isPrimitive_stdAddChar p)
    rw [ZMod.card] at hprod
    have hall : ∀ i, ‖rootEnum (lRoots f) i‖ = Real.sqrt p := by
      refine eq_of_prod_eq_pow (Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos))
        (fun i => norm_nonneg _) (norm_rootEnum_le hp2 hsq hsplit hm) ?_
      rw [← norm_prod, Finset.prod_eq_multiset_prod, univ_map_rootEnum, hprod, Fintype.card_fin,
        Multiset.length_toList, card_lRoots f hm]
    intro ω hω
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Multiset.mem_toList.mpr hω)
    rw [← hi]
    exact hall i
  · intro E _ _ _
    rw [extHyp_eq_powerSumW hF hsplit,
      powerSumW_eq_neg_rootPowerSum hF hsq hsplit hm Module.finrank_pos, rootPowerSum]

/-- **Counting points by the quadratic character**: `#{(x, y) ∈ E² : y² = f(x)} = |E| + Σ_x χ(f(x))`
for `E` of odd characteristic. -/
theorem card_points_eq {E : Type*} [Field E] [Fintype E] (hE : ringChar E ≠ 2) (f : E[X]) :
    ((univ.filter fun q : E × E => q.2 ^ 2 = f.eval q.1).card : ℤ) =
      (∑ x : E, quadraticChar E (f.eval x) : ℤ) + Fintype.card E := by
  rw [card_filter, ← univ_product_univ, sum_product]
  push_cast
  have : ∀ x : E, ((∑ y : E, if y ^ 2 = f.eval x then 1 else 0 : ℕ) : ℤ) =
      quadraticChar E (f.eval x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hE (f.eval x), Set.toFinset_setOf, ← card_filter]
  rw [show (Fintype.card E : ℤ) = ∑ _x : E, (1 : ℤ) by simp, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← this x]
  push_cast
  rfl

/-- **The Hasse–Weil bound** for `y² = f(x)` over every finite extension `E` of `𝔽_p`:
`|#{(x, y) ∈ E² : y² = f(x)} − |E|| ≤ (m − 1) √|E|`. -/
theorem abs_card_points_sub_le_splitHyperelliptic (hp2 : p ≠ 2) {f : (ZMod p)[X]}
    (hsq : Squarefree f) (hsplit : f.Splits) (hodd : Odd f.natDegree) (E : Type*) [Field E]
    [Fintype E] [Algebra (ZMod p) E] :
    |((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) - Fintype.card E| ≤
      (f.natDegree - 1 : ℕ) * Real.sqrt (Fintype.card E) := by
  obtain ⟨hcardω, hnorm, hsum⟩ := riemannHypothesis_splitHyperelliptic hp2 hsq hsplit hodd
  have hF := ringChar_zmod_ne_two hp2
  have hE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq (ZMod p) E]
  set n := Module.finrank (ZMod p) E
  have hcardE : Fintype.card E = p ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hcount := card_points_eq hE (f.map (algebraMap (ZMod p) E))
  simp only [eval_map, ← aeval_def] at hcount
  have hR : ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) - Fintype.card E =
      ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcount
    push_cast at this ⊢
    linarith
  rw [hR]
  have hC : ‖((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ)‖ =
      |((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ)| := by
    rw [show (((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ)) =
      (((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← hC]
  have hext : ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) = extHyp (E := E) f := by
    unfold extHyp; push_cast; rfl
  rw [hext, hsum E, norm_neg]
  calc ‖((lRoots f).map (· ^ n)).sum‖ ≤ ((lRoots f).map (fun ω => ‖ω ^ n‖)).sum := by
        simpa [Multiset.map_map] using norm_multiset_sum_le ((lRoots f).map (· ^ n))
    _ = ((lRoots f).map (fun _ => Real.sqrt p ^ n)).sum := by
        congr 1
        exact Multiset.map_congr rfl fun ω hω => by rw [norm_pow, hnorm ω hω]
    _ = (f.natDegree - 1 : ℕ) * Real.sqrt (Fintype.card E) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcardω, nsmul_eq_mul, hcardE,
          Nat.cast_pow]
        congr 1
        rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm,
          pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end GaloisForLFunctions.RHTower.Hyperelliptic
