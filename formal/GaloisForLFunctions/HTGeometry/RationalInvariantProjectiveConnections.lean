import GaloisForLFunctions.HTGeometry.RationalInvariantConnections

/-!
# Rational projective connections invariant under a rational map

Let `R` be a rational map of degree `d ≥ 2` over an algebraically closed field of characteristic
zero, and `γ` a rational projective connection with `R^*γ = γ`, i.e. `γ = γ(R)·R'² + S(R)`.

* **Double poles.**  In every chart `γ` has at most double poles.
* **Orbifold exponents.**  The double-pole coefficient is `(1 − μ²)/2` for a nonnegative rational
  `μ`, and `μ_p = e_p·μ_{R p}`: the points where `1 − 2c` is not the square of a nonnegative
  rational
  form a finite backward-invariant set on which `1 − 2c` scales by `d²` along cycles.
* **The orbifold connection.**  `a = Σ (μ_z − 1)/(x − z)` is an invariant affine connection.  The
  difference `R^*a − a` is a form with simple poles over `∞` only, with residues `e_z·ε`, where
  `ε` measures the failure of `Σ (1 − μ_p) = 2`; the residue theorem and `Σ_{R z = ∞} e_z = d` give
  `(d − 1)·ε = 0`.
* **Rigidity.**  `γ − (a' − a²/2)` is an invariant quadratic differential with at most a simple pole
  at a fixed point whose multiplier is not a root of unity, hence zero.  So `γ = a' − a²/2`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### The projective connection of an affine connection -/

/-- The projective connection `a' − a²/2` of an affine connection `a`. -/
def schConn (a : RatFunc K) : RatFunc K := ratFuncDeriv a - a ^ 2 / 2

/-- **Affine connections pull back to projective connections.** -/
theorem projPull_schConn {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c) (a : RatFunc K) :
    projPull P hP (schConn a) = schConn (connPull P hP a) := by
  have hP' := ratFuncDeriv_ne_zero_of_nonconst' hP
  have hP'' : ratFuncDeriv (ratFuncDeriv P) = logDerivRat (ratFuncDeriv P) * ratFuncDeriv P := by
    rw [logDerivRat]; field_simp
  rw [schConn, schConn, projPull, connPull, schwarzRat, ratFuncDeriv_add, ratFuncDeriv_mul,
    ratFuncDeriv_substitution, hP'', map_sub, map_div₀, map_pow, map_ofNat]
  ring

theorem projPull_sub {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c) (γ₁ γ₂ : RatFunc K) :
    projPull P hP γ₁ - projPull P hP γ₂
      = ratFuncSubstitutionAlgHom P hP (γ₁ - γ₂) * ratFuncDeriv P ^ 2 := by
  rw [projPull, projPull, map_sub]
  ring

theorem ratDpc_sub {f g : RatFunc K} {z : K} (hf : -2 ≤ ratOrder f z) (hg : -2 ≤ ratOrder g z) :
    ratDpc (f - g) z = ratDpc f z - ratDpc g z := by
  rw [ratDpc, ratDpc, ratDpc, mul_sub,
    ratValue_sub (ratOrder_linFac_sq_mul_nonneg hf) (ratOrder_linFac_sq_mul_nonneg hg)]

/-- **The double-pole coefficient of `a' − a²/2`** at a simple pole of residue `r` is
`(1 − (r + 1)²)/2`. -/
theorem schConn_dpc {f : RatFunc K} {z : K} (hf : -1 ≤ ratOrder f z) :
    -2 ≤ ratOrder (schConn f) z ∧ ratDpc (schConn f) z = (1 - (ratResidue f z + 1) ^ 2) / 2 := by
  have hsplit : schConn f = ratFuncDeriv f + RatFunc.C (-1 / 2) * f ^ 2 := by
    rw [schConn, map_div₀, map_neg, map_one, map_ofNat]
    ring
  obtain ⟨hd1, hd2⟩ := ratDpc_deriv hf
  obtain ⟨hs1, hs2⟩ := ratDpc_sq hf
  have hC := ratOrder_mul_ge_two (ratOrder_C_nonneg (-1 / 2 : K) z) hs1
  rw [hsplit]
  refine ⟨le_ratOrder_add (by norm_num) hd1 hC, ?_⟩
  rw [ratDpc_add hd1 hC, hd2, ratDpc_mul_regular (ratOrder_C_nonneg _ z) hs1, ratValue_C, hs2]
  ring

omit [CharZero K] in
/-- A function with at most a double pole and no double-pole term has at most a simple pole. -/
theorem ord_ge_neg_one_of_dpc_eq_zero {f : RatFunc K} {z : K} (hf : -2 ≤ ratOrder f z)
    (h : ratDpc f z = 0) : -1 ≤ ratOrder f z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [ratOrder_zero]; norm_num
  have hreg := ratOrder_linFac_sq_mul_nonneg hf
  have h0 : ratLinFac z ^ 2 * f ≠ 0 := mul_ne_zero (pow_ne_zero _ (ratLinFac_ne_zero z)) hf0
  have hpos := (ratValue_eq_zero_iff h0 hreg).mp h
  rw [ratOrder_mul (pow_ne_zero _ (ratLinFac_ne_zero z)) hf0, ratOrder_pow (ratLinFac_ne_zero z),
    ratOrder_linFac_self] at hpos
  omega

/-- The squared exponent `1 − 2c` of a projective connection with double-pole coefficient `c`. -/
def projExp (γ : RatFunc K) (p : Option K) : K :=
  1 - 2 * ratDpc (projAt γ p) (sphereCoord p)

theorem projExp_eq_one_of_simple {γ : RatFunc K} {p : Option K}
    (h : -1 ≤ ratOrder (projAt γ p) (sphereCoord p)) : projExp γ p = 1 := by
  rw [projExp, ratDpc_eq_zero_of_simple h]
  ring

/-! ### Invariant projective connections -/

variable [IsAlgClosed K] {R : RatFunc K}

/-- **An invariant projective connection has at most double poles, in every chart.** -/
theorem projAt_ord_ge_of_invariant (hR : ¬ ∃ c : K, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {γ : RatFunc K} (hγ : projPull R hR γ = γ) (p : Option K) :
    -2 ≤ ratOrder (projAt γ p) (sphereCoord p) := by
  set S := {p : Option K | ratOrder (projAt γ p) (sphereCoord p) ≤ -3} with hSdef
  have hSfin : S.Finite := (finite_chart_support (projAt γ) γ (projAt_some γ)).subset
    fun p hp => by
      simp only [hSdef, Set.mem_setOf_eq] at hp ⊢
      omega
  have hne : ∀ q ∈ S, projAt γ q ≠ 0 := fun q hq h0 => by
    simp only [hSdef, Set.mem_setOf_eq, h0, ratOrder_zero] at hq
    omega
  have hpre : ∀ q, ptImage R q ∈ S → q ∈ S := by
    intro q hq
    have h := projAt_projPull_ord hR γ q (hne _ hq) hq
    rw [hγ] at h
    have he := locDeg_pos hR q
    simp only [hSdef, Set.mem_setOf_eq] at hq ⊢
    rw [h]
    nlinarith
  have hzero := eq_zero_of_scaling_on_backward_invariant (exists_ptImage_eq hR) hSfin hpre
    (fun q => ratOrder (projAt γ q) (sphereCoord q) + 2) (natCast_pow_ne_one hd)
    fun q hq huniq => by
      have hRq : ptImage R q ∈ S :=
        (preimage_subset_finite (exists_ptImage_eq hR) hSfin hpre q hq).1
      have h := projAt_projPull_ord hR γ q (hne _ hRq) hRq
      rw [hγ, locDeg_eq_of_unique hR q huniq] at h
      show ratOrder (projAt γ q) (sphereCoord q) + 2
        = (ratFuncDegree R : ℤ)
          * (ratOrder (projAt γ (ptImage R q)) (sphereCoord (ptImage R q)) + 2)
      rw [h]
      ring
  by_contra hcon
  have hp : p ∈ S := by simp only [hSdef, Set.mem_setOf_eq]; omega
  have := hzero p hp
  omega

/-- The squared exponent scales by the square of the local degree. -/
theorem projExp_step (hR : ¬ ∃ c : K, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {γ : RatFunc K} (hγ : projPull R hR γ = γ) (p : Option K) :
    projExp γ p = (locDeg (R := R) p : K) ^ 2 * projExp γ (ptImage R p) := by
  have h := (projAt_projPull_dpc hR γ p (projAt_ord_ge_of_invariant hR hd hγ _)).2
  rw [hγ] at h
  rw [projExp, projExp, h]
  ring

/-- **The exponents are nonnegative rationals.** -/
theorem exists_rat_sqrt_projExp (hR : ¬ ∃ c : K, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {γ : RatFunc K} (hγ : projPull R hR γ = γ) (p : Option K) :
    ∃ μ : ℚ, 0 ≤ μ ∧ projExp γ p = (μ : K) ^ 2 := by
  set S := {p : Option K | ¬ ∃ μ : ℚ, 0 ≤ μ ∧ projExp γ p = (μ : K) ^ 2} with hSdef
  have hSfin : S.Finite := (finite_chart_support (projAt γ) γ (projAt_some γ)).subset
    fun p hp h0 => hp ⟨1, zero_le_one, by
      rw [projExp_eq_one_of_simple (by rw [h0]; norm_num)]
      norm_num⟩
  have hpre : ∀ q, ptImage R q ∈ S → q ∈ S := by
    intro q hq hqs
    obtain ⟨μ, hμ0, hμ⟩ := hqs
    apply hq
    have he := locDeg_pos hR q
    have he' : (locDeg (R := R) q : K) ≠ 0 := by exact_mod_cast he.ne'
    refine ⟨μ / (locDeg (R := R) q : ℚ), div_nonneg hμ0 (by exact_mod_cast he.le), ?_⟩
    rw [projExp_step hR hd hγ q] at hμ
    push_cast
    rw [div_pow, eq_div_iff (pow_ne_zero 2 he'), mul_comm]
    exact hμ
  have hd2 : 2 ≤ ratFuncDegree R ^ 2 := by nlinarith
  have hzero := eq_zero_of_scaling_on_backward_invariant (exists_ptImage_eq hR) hSfin hpre
    (projExp γ) (natCast_pow_ne_one hd2) fun q _ huniq => by
      rw [projExp_step hR hd hγ q, locDeg_eq_of_unique hR q huniq]
      push_cast
      ring
  by_contra hcon
  exact hcon ⟨0, le_rfl, by rw [hzero p hcon]; norm_num⟩

/-- **The exponents are multiplied by the local degree.** -/
theorem projExp_sqrt_step (hR : ¬ ∃ c : K, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {γ : RatFunc K} (hγ : projPull R hR γ = γ) (μ : Option K → ℚ) (hμ0 : ∀ p, 0 ≤ μ p)
    (hμ : ∀ p, projExp γ p = (μ p : K) ^ 2) (p : Option K) :
    μ p = (locDeg (R := R) p : ℚ) * μ (ptImage R p) := by
  have h := projExp_step hR hd hγ p
  rw [hμ, hμ] at h
  have hq : (μ p) ^ 2 = ((locDeg (R := R) p : ℚ) * μ (ptImage R p)) ^ 2 := by
    apply Rat.cast_injective (α := K)
    push_cast
    rw [h]
    ring
  exact (sq_eq_sq₀ (hμ0 p) (mul_nonneg (by exact_mod_cast (locDeg_pos hR p).le) (hμ0 _))).mp hq

/-- **The fibre over infinity.**  The finite preimages of `∞` are the zeros of `1/R`, and the local
degrees over `∞` add up to `deg R`. -/
theorem fibre_infty_sum [DecidableEq K] (hR : ¬ ∃ c : K, R = RatFunc.C c) :
    (∀ z, ptImage R (some z) = none ↔ z ∈ (fibreFn R none).num.roots.toFinset) ∧
      ∑ z ∈ (fibreFn R none).num.roots.toFinset, locDeg (R := R) (some z)
        + (if ptImage R none = none then locDeg (R := R) none else 0) = ratFuncDegree R := by
  obtain ⟨hmem, hsum⟩ := sum_locDeg_fibre hR none
  set T := fibreFn R none with hTdef
  have hsome : ∀ z, some z ∈ zeroSet T ↔ z ∈ T.num.roots.toFinset := fun z => by
    rw [zeroSet, Finset.mem_union, Finset.mem_image]
    split_ifs <;> simp
  have hnone : none ∈ zeroSet T ↔ T.num.natDegree < T.denom.natDegree := by
    rw [zeroSet, Finset.mem_union, Finset.mem_image]
    split_ifs with h <;> simp [h]
  refine ⟨fun z => (hmem (some z)).symm.trans (hsome z), ?_⟩
  have hdisj : Disjoint (T.num.roots.toFinset.image some)
      (if T.num.natDegree < T.denom.natDegree then ({none} : Finset (Option K)) else ∅) := by
    rw [Finset.disjoint_left]
    intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    split_ifs <;> simp
  rw [zeroSet, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => Option.some_inj.mp h)] at hsum
  rw [← hsum]
  congr 1
  have hc : ptImage R none = none ↔ T.num.natDegree < T.denom.natDegree :=
    (hmem none).symm.trans hnone
  by_cases h : T.num.natDegree < T.denom.natDegree
  · rw [if_pos (hc.mpr h), if_pos h, Finset.sum_singleton]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, Finset.sum_empty]

/-- **The orbifold connection of an invariant projective connection is invariant**, and the
projective connection differs from `a' − a²/2` by a function with at most simple poles. -/
theorem exists_invariant_connection_of_invariant_projective (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) {γ : RatFunc K} (hγ : projPull R hR γ = γ) :
    ∃ a : RatFunc K, connPull R hR a = a ∧ ∀ z : K, -1 ≤ ratOrder (γ - schConn a) z := by
  classical
  choose μ hμ0 hμ using exists_rat_sqrt_projExp hR hd hγ
  have hstep := projExp_sqrt_step hR hd hγ μ hμ0 hμ
  have hordγ := projAt_ord_ge_of_invariant hR hd hγ
  have hμreg : ∀ p, -1 ≤ ratOrder (projAt γ p) (sphereCoord p) → μ p = 1 := by
    intro p hp
    have h := hμ p
    rw [projExp_eq_one_of_simple hp] at h
    have : (μ p) ^ 2 = 1 ^ 2 := by
      apply Rat.cast_injective (α := K)
      rw [Rat.cast_pow, Rat.cast_pow, Rat.cast_one, one_pow, ← h]
    exact (sq_eq_sq₀ (hμ0 p) zero_le_one).mp this
  set S := γ.denom.roots.toFinset with hSdef
  have hSγ : ∀ z, z ∉ S → -1 ≤ ratOrder γ z := fun z hz => by
    by_contra h
    exact hz (Multiset.mem_toFinset.mpr ((mem_roots (RatFunc.denom_ne_zero γ)).mpr
      (ratOrder_neg_iff_denom_isRoot (by omega))))
  set a := ∑ z ∈ S, RatFunc.C ((μ (some z) : K) - 1) * (ratLinFac z)⁻¹ with hadef
  have hreg_off : ∀ z w, w ≠ z →
      0 ≤ ratOrder (RatFunc.C ((μ (some z) : K) - 1) * (ratLinFac z)⁻¹) w := fun z w hwz =>
    le_ratOrder_C_mul le_rfl _ (by rw [ratOrder_inv_linFac_of_ne hwz])
  have hterm_ord : ∀ z w, -1 ≤ ratOrder (RatFunc.C ((μ (some z) : K) - 1) * (ratLinFac z)⁻¹) w := by
    intro z w
    by_cases hwz : w = z
    · subst hwz
      exact le_ratOrder_C_mul (by norm_num) _ (by rw [ratOrder_inv_linFac])
    · have := hreg_off z w hwz
      omega
  have ha_ord : ∀ z, -1 ≤ ratOrder a z := fun z =>
    le_ratOrder_sum S _ (by norm_num) fun w _ => hterm_ord w z
  have ha_res : ∀ z, ratResidue a z = (μ (some z) : K) - 1 := by
    intro z
    rw [hadef, ratResidue_sum S _ (fun w _ => hterm_ord w z)]
    by_cases hz : z ∈ S
    · rw [Finset.sum_eq_single z (fun w _ hwz => ratResidue_eq_zero_of_regular
        (hreg_off w z (Ne.symm hwz))) (fun h => absurd hz h),
        ratResidue_C_mul _ (by rw [ratOrder_inv_linFac]), ratResidue_inv_linFac, mul_one]
    · rw [Finset.sum_eq_zero fun w hw => ratResidue_eq_zero_of_regular
        (hreg_off w z fun h => hz (h ▸ hw)),
        hμreg (some z) (by rw [projAt_some]; exact hSγ z hz)]
      push_cast
      ring
  have ha_inf : -1 ≤ ratOrder (infForm a) 0 := by
    rw [hadef, infForm_sum]
    exact le_ratOrder_sum S _ (by norm_num) fun z _ => by
      rw [infForm_C_mul]
      exact le_ratOrder_C_mul (by norm_num) _ (infForm_inv_linFac z).1
  have hconn_ord : ∀ p, -1 ≤ ratOrder (connAt a p) (sphereCoord p) := by
    intro p
    cases p with
    | some z => rw [connAt_some]; exact ha_ord z
    | none =>
        rw [connAt_none]
        exact le_ratOrder_add (by norm_num) ha_inf logDerivRat_deriv_invX.1
  set ε : K := ratResidue (connAt a none) 0 + 1 - μ none with hεdef
  have hconn_res : ∀ p, ratResidue (connAt a p) (sphereCoord p) + 1
      = μ p + (if p = none then ε else 0) := by
    intro p
    cases p with
    | some z =>
        rw [connAt_some, ha_res, if_neg (Option.some_ne_none z)]
        show ((μ (some z) : K) - 1) + 1 = _
        ring
    | none =>
        rw [if_pos rfl, hεdef]
        show ratResidue (connAt a none) 0 + 1 = _
        ring
  have hb : ∀ p, -1 ≤ ratOrder (connAt (connPull R hR a) p) (sphereCoord p) ∧
      ratResidue (connAt (connPull R hR a) p) (sphereCoord p) + 1
        = μ p + (locDeg (R := R) p : K) * (if ptImage R p = none then ε else 0) := by
    intro p
    obtain ⟨h1, h2⟩ := connAt_connPull_res hR a p (hconn_ord _)
    refine ⟨h1, ?_⟩
    rw [h2, hconn_res, hstep p]
    push_cast
    ring
  set δ := connPull R hR a - a with hδdef
  have hδ_ord : ∀ z, -1 ≤ ratOrder δ z := fun z => by
    have := (hb (some z)).1
    rw [connAt_some] at this
    exact le_ratOrder_sub (by norm_num) this (ha_ord z)
  have hδ_res : ∀ z, ratResidue δ z
      = (locDeg (R := R) (some z) : K) * (if ptImage R (some z) = none then ε else 0) := by
    intro z
    have h1 := hb (some z)
    have h2 := hconn_res (some z)
    rw [connAt_some] at h1 h2
    rw [if_neg (Option.some_ne_none z)] at h2
    have h1o : -1 ≤ ratOrder (connPull R hR a) z := h1.1
    have h1' : ratResidue (connPull R hR a) z + 1 = _ := h1.2
    have h2' : ratResidue a z + 1 = _ := h2
    rw [hδdef, ratResidue_sub h1o (ha_ord z)]
    linear_combination h1' - h2'
  have hδ_inf_ord : -1 ≤ ratOrder (infForm δ) 0 := by
    rw [hδdef, ← connAt_none_sub]
    exact le_ratOrder_sub (by norm_num) (hb none).1 (hconn_ord none)
  have hδ_inf_res : ratResidue (infForm δ) 0
      = (locDeg (R := R) none : K) * (if ptImage R none = none then ε else 0) - ε := by
    have hbo : -1 ≤ ratOrder (connAt (connPull R hR a) none) 0 := (hb none).1
    have hao : -1 ≤ ratOrder (connAt a none) 0 := hconn_ord none
    rw [hδdef, ← connAt_none_sub, ratResidue_sub hbo hao]
    have h1 : ratResidue (connAt (connPull R hR a) none) 0 + 1 = _ := (hb none).2
    have h2 : ratResidue (connAt a none) 0 + 1 = _ := hconn_res none
    rw [if_pos rfl] at h2
    linear_combination h1 - h2
  obtain ⟨hfib_mem, hfib_sum⟩ := fibre_infty_sum hR
  set T := (fibreFn R none).num.roots.toFinset with hTdef
  set S' := δ.denom.roots.toFinset ∪ T with hS'def
  have hS' : ∀ z, ratOrder δ z < 0 → z ∈ S' := fun z hz =>
    Finset.mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots (RatFunc.denom_ne_zero δ)).mpr
      (ratOrder_neg_iff_denom_isRoot hz)))
  have hres := sum_ratRes_add_infRes S' hS' hδ_ord hδ_inf_ord
  have hsum : ∑ z ∈ S', ratResidue δ z = ε * ∑ z ∈ T, (locDeg (R := R) (some z) : K) := by
    rw [Finset.sum_congr rfl fun z _ => hδ_res z, Finset.mul_sum]
    have hite : ∀ z, (locDeg (R := R) (some z) : K) * (if ptImage R (some z) = none then ε else 0)
        = if z ∈ T then ε * (locDeg (R := R) (some z) : K) else 0 := by
      intro z
      by_cases h : z ∈ T
      · rw [if_pos ((hfib_mem z).mpr h), if_pos h, mul_comm]
      · rw [if_neg (fun h' => h ((hfib_mem z).mp h')), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun z _ => hite z, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr Finset.subset_union_right]
  have hdK : ((ratFuncDegree R : ℤ) : K) - 1 ≠ 0 := by
    have : ((ratFuncDegree R : ℤ) : K) ≠ 1 := by
      intro h
      have := (natCast_pow_ne_one (M := K) hd) 1 one_pos
      rw [pow_one] at this
      exact this (by exact_mod_cast h)
    exact sub_ne_zero.mpr this
  have hfibK := congrArg (fun n : ℤ => (n : K)) hfib_sum
  simp only [Int.cast_add, Int.cast_sum] at hfibK
  have hε : ε = 0 := by
    rw [hsum, hδ_inf_res] at hres
    by_cases hc : ptImage R none = none
    · rw [if_pos hc] at hres hfibK
      have : ε * (((ratFuncDegree R : ℤ) : K) - 1) = 0 := by
        rw [← hfibK]
        linear_combination hres
      exact (mul_eq_zero.mp this).resolve_right hdK
    · rw [if_neg hc] at hres hfibK
      have : ε * (((ratFuncDegree R : ℤ) : K) - 1) = 0 := by
        rw [← hfibK]
        push_cast
        linear_combination hres
      exact (mul_eq_zero.mp this).resolve_right hdK
  have hδ0 : δ = 0 := by
    rw [eq_sum_polar S' hS' hδ_ord hδ_inf_ord]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [hδ_res, hε]
    simp
  refine ⟨a, sub_eq_zero.mp hδ0, fun z => ?_⟩
  have hγz : -2 ≤ ratOrder γ z := by
    have h := hordγ (some z)
    rw [projAt_some] at h
    exact h
  obtain ⟨hs1, hs2⟩ := schConn_dpc (ha_ord z)
  apply ord_ge_neg_one_of_dpc_eq_zero (le_ratOrder_sub (by norm_num) hγz hs1)
  rw [ratDpc_sub hγz hs1, hs2, ha_res]
  have hm : 1 - 2 * ratDpc γ z = (μ (some z) : K) ^ 2 := by
    have := hμ (some z)
    rw [projExp, projAt_some] at this
    exact this
  linear_combination (-1 / 2 : K) * hm

omit [IsAlgClosed K] in
/-- **Rigidity of invariant quadratic differentials.**  At a fixed point `0` whose multiplier is
nonzero and not a root of unity, an invariant `q = q(R)·R'²` with at most a simple pole vanishes. -/
theorem eq_zero_of_invariant_quadratic_differential (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0) (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1) {q : RatFunc K}
    (hq : q = ratFuncSubstitutionAlgHom R hR q * ratFuncDeriv R ^ 2)
    (hq0 : -1 ≤ ratOrder q 0) : q = 0 := by
  by_contra hne
  have h := const_mul_pow_eq_one_at_fixed_point hR h0 hR0 hlam0 hne (κ := 1) (N := 2)
    (by rw [map_one, one_mul]; exact hq)
  rw [one_mul] at h
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ ratOrder q 0 + 2 by omega)
  rw [show ratOrder q 0 + ((2 : ℕ) : ℤ) = ratOrder q 0 + 2 by norm_num, hn, zpow_natCast] at h
  exact hlam n (by omega) h

/-- **An invariant projective connection comes from an invariant affine connection.** -/
theorem exists_schConn_of_invariant_projective (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1) {γ : RatFunc K}
    (hγ : projPull R hR γ = γ) : ∃ a : RatFunc K, connPull R hR a = a ∧ γ = schConn a := by
  obtain ⟨a, ha, hord⟩ := exists_invariant_connection_of_invariant_projective hR hd hγ
  refine ⟨a, ha, ?_⟩
  have hq : γ - schConn a
      = ratFuncSubstitutionAlgHom R hR (γ - schConn a) * ratFuncDeriv R ^ 2 := by
    rw [← projPull_sub, hγ, projPull_schConn, ha]
  exact sub_eq_zero.mp
    (eq_zero_of_invariant_quadratic_differential hR h0 hR0 hlam0 hlam hq (hord 0))

/-- **An invariant projective connection yields a rational cocycle.** -/
theorem ratCocycle_of_invariant_projective (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam0 : ratValue (ratFuncDeriv R) 0 ≠ 0)
    (hlam : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1) {γ : RatFunc K}
    (hγ : projPull R hR γ = γ) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ B : RatFunc K, B ≠ 0 ∧
      ratFuncDeriv R ^ N * B
        = RatFunc.C (ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + j))
          * ratFuncSubstitutionAlgHom R hR B := by
  obtain ⟨a, ha, -⟩ := exists_schConn_of_invariant_projective hR hd h0 hR0 hlam0 hlam hγ
  exact ratCocycle_of_invariant_connection hR hd h0 hR0 hlam0 ha

end

end GaloisForLFunctions.HTGeometry
