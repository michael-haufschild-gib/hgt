import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GreedyDegreesOfPowerSums
import GaloisForLFunctions.SignFreePurityMechanisms.TheUltrametricNewtonPolygonSeparatesTheRoots
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField

/-!
# The Goss zeta function of `𝔽_q[T]` at the negative integers

Let `q = p ^ s`. The value of the Goss zeta function of `𝔽_q[T]` at `−N` is
`ζ(x, −N) = ∑_{d ≥ 0} x^{−d} ∑_{a monic, deg a = d} ⟨a⟩ ^ N`, `⟨a⟩ = a / T^{deg a}`. The inner sums
are `T^{−dN} S_d(N)` and vanish for `d > N` (`monicPowerSum_eq_zero_of_lt`).

We work in `𝔽_p((1/T))`, realized as the Laurent series `𝔽_p((X))` with `X = 1/T` and the
`X`-adic norm, in which `‖T‖ > 1` and `‖P(T)‖ = ‖T‖ ^ deg P` for a nonzero `P ∈ 𝔽_p[T]`
(`norm_aeval_T`). The polynomial `Z_N(w) = ∑_d S_d(N) w^d` (`gossZetaPoly`) has coefficients in
`𝔽_p[T]` of norms `‖T‖ ^ deg S_d(N)`; by the greedy degree law these are nonzero up to the
degree and strictly log-concave. The ultrametric Newton polygon therefore has sides of length
one, and `Z_N` splits over `𝔽_p((1/T))` with simple roots of pairwise distinct norms
(`gossZetaPoly_splits`, `nodup_roots_gossZetaPoly`, `injOn_norm_roots_gossZetaPoly`).

**The Riemann hypothesis of Goss at `−N`** (`gossZetaNeg_eq_prod`): there are finitely many
pairwise distinct nonzero `x₁, …, x_D ∈ 𝔽_p((1/T))`, of pairwise distinct norms, such that in every
field `L` containing `𝔽_q` and `𝔽_p((1/T))`, `ζ(x, −N) = ∏ᵢ (1 − xᵢ / x)` for all `x ≠ 0`. Thus
all zeros of `x ↦ ζ(x, −N)`, in `ℂ_∞` or anywhere else, are simple and lie in `𝔽_p((1/T))`.
-/

open Finset Polynomial
open scoped LaurentSeries WithZero

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

open GaloisForLFunctions.RHTower.WeilKloosterman GaloisForLFunctions.HTGeometry.ABHN

variable (p : ℕ) [hp : Fact p.Prime]

/-- `𝔽_p((1/T)) = 𝔽_p((X))` with its `X`-adic norm is a nontrivially normed field. -/
noncomputable instance laurentSeriesZModNontriviallyNormedField :
    NontriviallyNormedField (LaurentSeries (ZMod p)) :=
  Valued.toNontriviallyNormedField (LaurentSeries (ZMod p)) ℤᵐ⁰

/-- The variable `T = X⁻¹` of `𝔽_p[T]` inside `𝔽_p((X))`. -/
noncomputable def varT : LaurentSeries (ZMod p) := HahnSeries.single (-1 : ℤ) (1 : ZMod p)

theorem one_lt_norm_varT : 1 < ‖varT p‖ := by
  rw [Valued.toNormedField.one_lt_norm_iff, varT, LaurentSeries.valuation_single_zpow]
  decide

theorem varT_ne_zero : varT p ≠ 0 := fun h => by
  have := one_lt_norm_varT p
  rw [h, norm_zero] at this
  exact absurd this (by norm_num)

/-- Nonzero constants are roots of unity, hence units of the norm. -/
theorem norm_algebraMap_zmod {c : ZMod p} (hc : c ≠ 0) :
    ‖algebraMap (ZMod p) (LaurentSeries (ZMod p)) c‖ = 1 := by
  have h := congrArg (fun y => ‖algebraMap (ZMod p) (LaurentSeries (ZMod p)) y‖)
    (ZMod.pow_card_sub_one_eq_one hc)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp1).mp h

theorem norm_algebraMap_zmod_le (c : ZMod p) :
    ‖algebraMap (ZMod p) (LaurentSeries (ZMod p)) c‖ ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, norm_zero]
    exact zero_le_one
  · exact (norm_algebraMap_zmod p hc).le

/-- **The degree is the norm.** `‖P(T)‖ = ‖T‖ ^ deg P` for nonzero `P ∈ 𝔽_p[T]`. -/
theorem norm_aeval_varT {P : (ZMod p)[X]} (hP : P ≠ 0) :
    ‖aeval (varT p) P‖ = ‖varT p‖ ^ P.natDegree := by
  have hc := one_lt_norm_varT p
  rw [aeval_def, eval₂_eq_sum_range, sum_range_succ]
  have htop : ‖algebraMap (ZMod p) _ (P.coeff P.natDegree) * varT p ^ P.natDegree‖ =
      ‖varT p‖ ^ P.natDegree := by
    rw [norm_mul, norm_pow, coeff_natDegree,
      norm_algebraMap_zmod p (leadingCoeff_ne_zero.mpr hP), one_mul]
  have hrest : ‖∑ i ∈ range P.natDegree, algebraMap (ZMod p) _ (P.coeff i) * varT p ^ i‖ <
      ‖varT p‖ ^ P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
    · rw [h0, range_zero, sum_empty, norm_zero, pow_zero]
      exact zero_lt_one
    · refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (C := ‖varT p‖ ^ (P.natDegree - 1)) (pow_nonneg (norm_nonneg _) _) fun i hi => ?_) ?_
      · rw [norm_mul, norm_pow]
        calc ‖algebraMap (ZMod p) _ (P.coeff i)‖ * ‖varT p‖ ^ i ≤ 1 * ‖varT p‖ ^ i :=
              mul_le_mul_of_nonneg_right (norm_algebraMap_zmod_le p _) (pow_nonneg (norm_nonneg _) _)
          _ ≤ ‖varT p‖ ^ (P.natDegree - 1) := by
              rw [one_mul]
              exact pow_le_pow_right₀ hc.le (by have := mem_range.mp hi; omega)
      · exact pow_lt_pow_right₀ hc (by omega)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [htop]; exact hrest.ne), htop,
    max_eq_right hrest.le]

theorem aeval_varT_ne_zero {P : (ZMod p)[X]} (hP : P ≠ 0) : aeval (varT p) P ≠ 0 := by
  intro h
  have := norm_aeval_varT p hP
  rw [h, norm_zero] at this
  exact absurd this.symm (pow_ne_zero _ (by linarith [one_lt_norm_varT p]))

/-! ### The power sums vanish beyond `N` -/

variable {p} {s : ℕ}

theorem le_of_digitChain {d : ℕ} {S : Finset (Digit p)} (c : DigitChain p s d S) :
    d ≤ digitValueNat p S := by
  rw [← c.sum_values_add_remainder]
  have h : ∀ i, 1 ≤ c.values i := fun i => by
    obtain ⟨x, hx⟩ := c.nonempty i
    exact le_trans (Nat.one_le_pow _ _ hp.out.pos)
      (single_le_sum (f := fun y : Digit p => p ^ y.1) (fun _ _ => Nat.zero_le _) hx)
  calc d = ∑ _i : Fin d, 1 := by simp
    _ ≤ ∑ i, c.values i := sum_le_sum fun i _ => h i
    _ ≤ _ := Nat.le_add_right _ _

variable [NeZero s]

theorem gossPoly_ne_zero_iff_digitsOf (F : Type*) [Field F] [CharP F p] (d N : ℕ) :
    gossPoly F (p ^ s) d N ≠ 0 ↔ Nonempty (DigitChain p s d (digitsOf p N)) := by
  conv_lhs => rw [← digitValueNat_digitsOf hp.out.two_le N]
  exact gossPoly_ne_zero_iff

theorem gossPoly_eq_zero_of_lt (F : Type*) [Field F] [CharP F p] {d N : ℕ} (h : N < d) :
    gossPoly F (p ^ s) d N = 0 := by
  by_contra hne
  obtain ⟨c⟩ := (gossPoly_ne_zero_iff_digitsOf F d N).mp hne
  have := le_of_digitChain c
  rw [digitValueNat_digitsOf hp.out.two_le N] at this
  omega

omit [NeZero s] in
/-- Over `𝔽_q`, `q = p ^ s`, the power sums `S_d(N)` are the images of the recursion over `𝔽_p`. -/
theorem monicPowerSum_eq_map (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq] [CharP Fq p]
    (hq : Fintype.card Fq = p ^ s) (d N : ℕ) :
    monicPowerSum Fq d N = (gossPoly (ZMod p) (p ^ s) d N).map (ZMod.castHom (dvd_refl p) Fq) := by
  rw [monicPowerSum_eq_gossPoly, hq, map_gossPoly]

theorem monicPowerSum_eq_zero_of_lt (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]
    [CharP Fq p] (hq : Fintype.card Fq = p ^ s) {d N : ℕ} (h : N < d) :
    monicPowerSum Fq d N = 0 := by
  rw [monicPowerSum_eq_gossPoly, hq]
  exact gossPoly_eq_zero_of_lt Fq h

/-! ### The zeta polynomial and its Newton polygon -/

variable (p s) in
/-- `Z_N(w) = ∑_{d ≤ N} S_d(N)(T) w ^ d` over `𝔽_p((1/T))`. -/
noncomputable def gossZetaPoly (N : ℕ) : (LaurentSeries (ZMod p))[X] :=
  ∑ d ∈ range (N + 1), monomial d (aeval (varT p) (gossPoly (ZMod p) (p ^ s) d N))

theorem coeff_gossZetaPoly (N d : ℕ) :
    (gossZetaPoly p s N).coeff d = aeval (varT p) (gossPoly (ZMod p) (p ^ s) d N) := by
  rw [gossZetaPoly, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [sum_ite_eq' (range (N + 1)) d]
  split_ifs with h
  · rfl
  · rw [gossPoly_eq_zero_of_lt (ZMod p) (by simpa using h), map_zero]

theorem coeff_gossZetaPoly_ne_zero_iff (N d : ℕ) :
    (gossZetaPoly p s N).coeff d ≠ 0 ↔ Nonempty (DigitChain p s d (digitsOf p N)) := by
  rw [coeff_gossZetaPoly, ← gossPoly_ne_zero_iff_digitsOf (ZMod p)]
  constructor
  · intro h hP
    exact h (by rw [hP, map_zero])
  · exact aeval_varT_ne_zero p

theorem coeff_zero_gossZetaPoly (N : ℕ) : (gossZetaPoly p s N).coeff 0 = 1 := by
  rw [coeff_gossZetaPoly, gossPoly_zero, map_one]

theorem gossZetaPoly_ne_zero (N : ℕ) : gossZetaPoly p s N ≠ 0 := fun h => by
  have := coeff_zero_gossZetaPoly (p := p) (s := s) N
  rw [h, coeff_zero] at this
  exact zero_ne_one this

omit hp [NeZero s] in
theorem nonempty_chain_of_add {S : Finset (Digit p)} {j : ℕ} :
    ∀ k, Nonempty (DigitChain p s (j + k) S) → Nonempty (DigitChain p s j S)
  | 0, h => h
  | k + 1, h => nonempty_chain_of_add k (nonempty_chain_of_succ h)

theorem coeff_gossZetaPoly_ne_zero_of_le (N : ℕ) {j : ℕ}
    (hj : j ≤ (gossZetaPoly p s N).natDegree) : (gossZetaPoly p s N).coeff j ≠ 0 := by
  have htop := (coeff_gossZetaPoly_ne_zero_iff N _).mp
    (leadingCoeff_ne_zero.mpr (gossZetaPoly_ne_zero (p := p) (s := s) N))
  rw [coeff_gossZetaPoly_ne_zero_iff]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  rw [hk] at htop
  exact nonempty_chain_of_add k htop

/-- **The Newton polygon has sides of length one.** -/
theorem gossZetaPoly_strict_logConcave (N : ℕ) (j : ℕ)
    (hj : j + 2 ≤ (gossZetaPoly p s N).natDegree) :
    ‖(gossZetaPoly p s N).coeff j‖ * ‖(gossZetaPoly p s N).coeff (j + 2)‖ <
      ‖(gossZetaPoly p s N).coeff (j + 1)‖ ^ 2 := by
  have hc := one_lt_norm_varT p
  have h2 := (coeff_gossZetaPoly_ne_zero_iff N (j + 2)).mp
    (coeff_gossZetaPoly_ne_zero_of_le N hj)
  have hne (k : ℕ) (hk : k ≤ j + 2) : gossPoly (ZMod p) (p ^ s) k N ≠ 0 := by
    rw [gossPoly_ne_zero_iff_digitsOf]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
    rw [hm] at h2
    exact nonempty_chain_of_add m h2
  have hconc := natDegree_gossPoly_strictConcave (F := ZMod p) (s := s) (d := j)
    (S := digitsOf p N) h2
  rw [digitValueNat_digitsOf hp.out.two_le N] at hconc
  simp only [coeff_gossZetaPoly, norm_aeval_varT p (hne _ le_rfl),
    norm_aeval_varT p (hne j (by omega)), norm_aeval_varT p (hne (j + 1) (by omega)), ← pow_add,
    ← pow_mul]
  exact pow_lt_pow_right₀ hc (by omega)

theorem gossZetaPoly_splits (N : ℕ) : (gossZetaPoly p s N).Splits :=
  splits_of_strict_logConcave _ (fun _ hj => coeff_gossZetaPoly_ne_zero_of_le N hj)
    (gossZetaPoly_strict_logConcave N)

/-- The roots have pairwise distinct norms: one root on each side of the Newton polygon. -/
theorem injOn_norm_roots_gossZetaPoly (N : ℕ) :
    Set.InjOn (fun z : LaurentSeries (ZMod p) => ‖z‖) {z | (gossZetaPoly p s N).IsRoot z} :=
  injOn_norm_isRoot _ (fun _ hj => coeff_gossZetaPoly_ne_zero_of_le N hj)
    (gossZetaPoly_strict_logConcave N)

/-- The roots are simple. -/
theorem nodup_roots_gossZetaPoly (N : ℕ) : (gossZetaPoly p s N).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [count_roots]
  by_contra hgt
  have hroot := (one_lt_rootMultiplicity_iff_isRoot (gossZetaPoly_ne_zero N)).mp (not_le.mp hgt)
  exact HasSimpleSlopes.derivative_eval_ne_zero
    (v := NormedField.toAbsoluteValue (LaurentSeries (ZMod p)))
    IsUltrametricDist.isNonarchimedean_norm
    ⟨fun _ hj => coeff_gossZetaPoly_ne_zero_of_le N hj, gossZetaPoly_strict_logConcave N⟩
    hroot.1 hroot.2

/-! ### The Goss zeta function at `−N` -/

variable (p) in
/-- The value at `−N` of the Goss zeta function of `𝔽_q[T]`, in a field `L` containing `𝔽_q`
(through `τ`) and `𝔽_p((1/T))` (through `σ`):
`ζ(x, −N) = ∑_d x^{−d} ∑_{a monic, deg a = d} (a(T) / T^d) ^ N`. The sum stops at `d = N`, beyond
which every inner sum is zero (`monicPowerSum_eq_zero_of_lt`). -/
noncomputable def gossZetaNeg (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]
    {L : Type*} [Field L] (σ : LaurentSeries (ZMod p) →+* L) (τ : Fq →+* L) (N : ℕ) (x : L) : L :=
  ∑ d ∈ range (N + 1), x⁻¹ ^ d *
    ∑ a ∈ monicDeg (F := Fq) d, (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) ^ N

/-- **The Riemann hypothesis for the Goss zeta function of `𝔽_q[T]` at `−N`.** There are
pairwise distinct nonzero `xᵢ ∈ 𝔽_p((1/T))` of pairwise distinct norms such that, in every field
`L ⊇ 𝔽_q, 𝔽_p((1/T))`, `ζ(x, −N) = ∏ᵢ (1 − xᵢ / x)` for `x ≠ 0`. Hence every zero is simple and
lies in `𝔽_p((1/T))`. -/
theorem gossZetaNeg_eq_prod (N : ℕ) :
    ∃ ρ : Multiset (LaurentSeries (ZMod p)), ρ.Nodup ∧ (∀ r ∈ ρ, r ≠ 0) ∧
      Set.InjOn (fun r : LaurentSeries (ZMod p) => ‖r‖) {r | r ∈ ρ} ∧
      ∀ (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq] [CharP Fq p],
        Fintype.card Fq = p ^ s →
        ∀ (L : Type*) [Field L] (σ : LaurentSeries (ZMod p) →+* L) (τ : Fq →+* L) (x : L),
          x ≠ 0 → gossZetaNeg p Fq σ τ N x = (ρ.map fun r => 1 - σ r / x).prod := by
  set f := gossZetaPoly p s N with hf
  set T := varT p
  have hT : T ≠ 0 := varT_ne_zero p
  have hroot0 : ∀ r ∈ f.roots, r ≠ 0 := by
    intro r hr h0
    rw [h0] at hr
    have h := (mem_roots (gossZetaPoly_ne_zero N)).mp hr
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_zero_gossZetaPoly] at h
    exact one_ne_zero h
  set g : LaurentSeries (ZMod p) → LaurentSeries (ZMod p) := fun r => (T ^ N * r)⁻¹
  have hg_inj : ∀ x ∈ f.roots, ∀ y ∈ f.roots, g x = g y → x = y := by
    intro x _ y _ hxy
    have h := inv_injective hxy
    exact mul_left_cancel₀ (pow_ne_zero N hT) h
  refine ⟨f.roots.map g, (nodup_roots_gossZetaPoly N).map_on hg_inj, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.mp hr
    exact inv_ne_zero (mul_ne_zero (pow_ne_zero N hT) (hroot0 r' hr'))
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hb
    simp only [g, norm_inv, norm_mul, norm_pow] at hab
    have hTN : 0 < ‖T‖ ^ N := pow_pos (norm_pos_iff.mpr hT) N
    have hab' : ‖a'‖ = ‖b'‖ := by
      have := inv_injective hab
      exact mul_left_cancel₀ hTN.ne' this
    have := injOn_norm_roots_gossZetaPoly (p := p) (s := s) N
      (isRoot_of_mem_roots ha') (isRoot_of_mem_roots hb') hab'
    rw [this]
  · intro Fq _ _ _ _ hq L _ σ τ x hx
    -- the inner sums are the images of the coefficients of `f`
    have hinner (d : ℕ) : ∑ a ∈ monicDeg (F := Fq) d, (eval₂ τ (σ T) a / σ T ^ d) ^ N =
        σ (f.coeff d) * ((σ T) ^ N)⁻¹ ^ d := by
      simp_rw [div_pow]
      rw [← sum_div]
      have hsum : ∑ a ∈ monicDeg (F := Fq) d, eval₂ τ (σ T) a ^ N =
          eval₂ τ (σ T) (monicPowerSum Fq d N) := by
        rw [monicPowerSum, eval₂_finsetSum]
        simp only [eval₂_pow]
      rw [hsum, monicPowerSum_eq_map Fq hq, eval₂_map,
        show τ.comp (ZMod.castHom (dvd_refl p) Fq) =
          σ.comp (algebraMap (ZMod p) (LaurentSeries (ZMod p))) from RingHom.ext_zmod _ _,
        ← hom_eval₂, coeff_gossZetaPoly]
      rw [← pow_mul, inv_pow, ← pow_mul, mul_comm N d, div_eq_mul_inv]
      rfl
    have hdeg : f.natDegree < N + 1 := by
      by_contra h
      have := coeff_gossZetaPoly_ne_zero_iff (p := p) (s := s) N f.natDegree
      rw [← hf] at this
      obtain ⟨c⟩ := this.mp (leadingCoeff_ne_zero.mpr (gossZetaPoly_ne_zero N))
      have := le_of_digitChain c
      rw [digitValueNat_digitsOf hp.out.two_le N] at this
      omega
    set w : L := x⁻¹ * ((σ T) ^ N)⁻¹
    have hzeta : gossZetaNeg p Fq σ τ N x = eval₂ σ w f := by
      rw [eval₂_eq_sum_range' σ hdeg, gossZetaNeg]
      refine sum_congr rfl fun d _ => ?_
      rw [hinner, mul_pow]
      ring
    -- factor `f` over its roots and normalize by `f(0) = 1`
    have hsplit := (gossZetaPoly_splits (p := p) (s := s) N).eq_prod_roots
    rw [← hf] at hsplit
    have h0 : f.leadingCoeff * (f.roots.map fun r => -r).prod = 1 := by
      have h := congrArg (eval 0) hsplit
      rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map] at h
      simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub] at h
      rw [← h, ← coeff_zero_eq_eval_zero, coeff_zero_gossZetaPoly]
    rw [hzeta]
    conv_lhs => rw [hsplit]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, Multiset.map_map]
    have hfac : ∀ r ∈ f.roots, (eval₂ σ w ∘ fun r => X - C r) r =
        σ (-r) * ((fun r => 1 - σ r / x) ∘ g) r := by
      intro r hr
      have hσr : σ r ≠ 0 := (map_ne_zero σ).mpr (hroot0 r hr)
      have hσT : σ T ≠ 0 := (map_ne_zero σ).mpr hT
      simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C, g, map_inv₀, map_mul,
        map_pow, map_neg, w]
      field_simp
      ring
    rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, ← mul_assoc]
    have hσ0 : σ f.leadingCoeff * (f.roots.map fun r => σ (-r)).prod = 1 := by
      rw [← map_one σ, ← h0, map_mul, map_multiset_prod, Multiset.map_map]
      rfl
    rw [hσ0, one_mul]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
