import GaloisForLFunctions.HTGeometry.RationalSimplePoleForms
import GaloisForLFunctions.HTGeometry.RittTransportConstant

/-!
# Rational affine connections invariant under a rational map

Let `R` be a rational map of degree `d ≥ 2` over an algebraically closed field of characteristic
zero, and `a` a rational affine connection with `R^*a = a`, i.e. `a = a(R)·R' + R''/R'`.

* **Simple poles.**  In every chart `a` has at most simple poles: the points with a pole of order at
  least two form a finite backward-invariant set, on which `ord + 1` scales by `d` along cycles.
* **Rational residues.**  Every residue is rational: the points with an irrational residue form a
  finite backward-invariant set, on which `res + 1` scales by `d` along cycles.
* **Logarithmic derivative.**  Hence `N·a = g'/g` for a positive integer `N` and a rational `g`, and
  `g = κ·g(R)·R'^N` for a constant `κ`.
* **The cocycle.**  At a fixed point `0` with multiplier `λ ≠ 0`, `κ·λ^{m+N} = 1` with
  `m = ord₀ g`, so `B = 1/g` satisfies `R'^N·B = λ^{N+m}·B(R)`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### Scaling along cycles of a backward-invariant set -/

/-- **Scaling on a finite backward-invariant set.**  If `h` is multiplied by `d` at each point of a
finite backward-invariant set which is the only preimage of its image, and no power of `d` is one,
then `h` vanishes on the set. -/
theorem eq_zero_of_scaling_on_backward_invariant {α M : Type*} [CommRing M] [IsDomain M]
    {f : α → α} (hf : Function.Surjective f) {S : Set α} (hS : S.Finite)
    (hpre : ∀ z, f z ∈ S → z ∈ S) (h : α → M) {d : M} (hd : ∀ n : ℕ, 0 < n → d ^ n ≠ 1)
    (hstep : ∀ z ∈ S, (∀ z', f z' = f z → z' = z) → h z = d * h (f z)) :
    ∀ z ∈ S, h z = 0 := by
  intro z hz
  have hinv := preimage_subset_finite hf hS hpre
  have hit : ∀ k, f^[k] z ∈ S := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact (hinv _ ih).1
  obtain ⟨-, -, m, hm, hper⟩ := hinv z hz
  refine eq_zero_of_scaling_on_cycle h hd hm hper fun k => ?_
  rw [Function.iterate_succ_apply']
  exact hstep _ (hit k) (hinv _ (hit k)).2.1

theorem natCast_pow_ne_one {M : Type*} [CommRing M] [CharZero M] {d : ℕ} (hd : 2 ≤ d) :
    ∀ n : ℕ, 0 < n → ((d : M)) ^ n ≠ 1 := by
  intro n hn h
  have h' : ((d ^ n : ℕ) : M) = ((1 : ℕ) : M) := by push_cast; exact h
  have h'' := Nat.cast_injective h'
  have : 2 ^ n ≤ d ^ n := Nat.pow_le_pow_left hd n
  have : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

variable [IsAlgClosed K] {R : RatFunc K}

/-! ### Simple poles and rational residues -/

/-- **An invariant affine connection has at most simple poles, in every chart.** -/
theorem connAt_ord_ge_of_invariant (hR : ¬ ∃ c : K, R = RatFunc.C c) (hd : 2 ≤ ratFuncDegree R)
    {a : RatFunc K} (ha : connPull R hR a = a) (p : Option K) :
    -1 ≤ ratOrder (connAt a p) (sphereCoord p) := by
  set S := {p : Option K | ratOrder (connAt a p) (sphereCoord p) ≤ -2} with hSdef
  have hSfin : S.Finite := (finite_chart_support (connAt a) a (connAt_some a)).subset
    fun p hp => by
      simp only [hSdef, Set.mem_setOf_eq] at hp ⊢
      omega
  have hne : ∀ q ∈ S, connAt a q ≠ 0 := fun q hq h0 => by
    simp only [hSdef, Set.mem_setOf_eq, h0, ratOrder_zero] at hq
    omega
  have hpre : ∀ q, ptImage R q ∈ S → q ∈ S := by
    intro q hq
    have h := connAt_connPull_ord hR a q (hne _ hq) hq
    rw [ha] at h
    have he := locDeg_pos hR q
    simp only [hSdef, Set.mem_setOf_eq] at hq ⊢
    rw [h]
    nlinarith
  have hzero := eq_zero_of_scaling_on_backward_invariant (exists_ptImage_eq hR) hSfin hpre
    (fun q => ratOrder (connAt a q) (sphereCoord q) + 1) (natCast_pow_ne_one hd)
    fun q hq huniq => by
      have hRq : ptImage R q ∈ S :=
        (preimage_subset_finite (exists_ptImage_eq hR) hSfin hpre q hq).1
      have h := connAt_connPull_ord hR a q (hne _ hRq) hRq
      rw [ha, locDeg_eq_of_unique hR q huniq] at h
      show ratOrder (connAt a q) (sphereCoord q) + 1
        = (ratFuncDegree R : ℤ)
          * (ratOrder (connAt a (ptImage R q)) (sphereCoord (ptImage R q)) + 1)
      rw [h]
      ring
  by_contra hcon
  have hp : p ∈ S := by simp only [hSdef, Set.mem_setOf_eq]; omega
  have := hzero p hp
  omega

/-- **An invariant affine connection has rational residues, in every chart.** -/
theorem connAt_res_rational_of_invariant (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) {a : RatFunc K} (ha : connPull R hR a = a) (p : Option K) :
    ∃ q : ℚ, ratResidue (connAt a p) (sphereCoord p) = q := by
  have hord := connAt_ord_ge_of_invariant hR hd ha
  set s : Option K → K := fun q => ratResidue (connAt a q) (sphereCoord q) + 1 with hsdef
  set S := {p : Option K | ¬ ∃ q : ℚ, s p = q} with hSdef
  have hSfin : S.Finite := (finite_chart_support (connAt a) a (connAt_some a)).subset
    fun p hp h0 => hp ⟨1, by
      simp only [hsdef]
      rw [ratResidue_eq_zero_of_regular (le_of_eq h0.symm)]
      norm_num⟩
  have hstep : ∀ q, s q = (locDeg (R := R) q : K) * s (ptImage R q) := by
    intro q
    have h := (connAt_connPull_res hR a q (hord _)).2
    rw [ha] at h
    exact h
  have hpre : ∀ q, ptImage R q ∈ S → q ∈ S := by
    intro q hq hqs
    obtain ⟨r, hr⟩ := hqs
    apply hq
    have he : (locDeg (R := R) q : K) ≠ 0 := by exact_mod_cast (locDeg_pos hR q).ne'
    refine ⟨r / (locDeg (R := R) q : ℚ), ?_⟩
    rw [hstep q] at hr
    push_cast
    field_simp
    rw [← hr]
    ring
  have hzero := eq_zero_of_scaling_on_backward_invariant (exists_ptImage_eq hR) hSfin hpre s
    (natCast_pow_ne_one hd) fun q _ huniq => by
      rw [hstep q, locDeg_eq_of_unique hR q huniq]
      push_cast
      ring
  by_contra hcon
  have hp : p ∈ S := fun ⟨r, hr⟩ => hcon ⟨r - 1, by
    push_cast
    rw [← hr]
    ring⟩
  exact hp ⟨0, by rw [hzero p hp]; norm_num⟩

omit [IsAlgClosed K] in
theorem logDerivRat_prod_linFac (S : Finset K) (n : K → ℤ) :
    logDerivRat (∏ z ∈ S, ratLinFac z ^ n z) = ∑ z ∈ S, (n z : RatFunc K) * (ratLinFac z)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, logDerivRat_one]
  | insert z S hz ih =>
      rw [Finset.prod_insert hz, Finset.sum_insert hz,
        logDerivRat_mul (zpow_ne_zero _ (ratLinFac_ne_zero z))
          (Finset.prod_ne_zero_iff.mpr fun w _ => zpow_ne_zero _ (ratLinFac_ne_zero w)),
        logDerivRat_zpow_linFac, ih]

/-- **An invariant affine connection is a rational multiple of a logarithmic derivative.** -/
theorem exists_logDeriv_of_invariant_connection (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) {a : RatFunc K} (ha : connPull R hR a = a) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : RatFunc K, g ≠ 0 ∧ (N : RatFunc K) * a = logDerivRat g := by
  classical
  have hord := connAt_ord_ge_of_invariant hR hd ha
  have hres := connAt_res_rational_of_invariant hR hd ha
  have hfin : ∀ z, -1 ≤ ratOrder a z := fun z => by
    have := hord (some z)
    rwa [connAt_some] at this
  have hinf : -1 ≤ ratOrder (infForm a) 0 := (infForm_ord_of_connAt (hord none)).1
  set S := a.denom.roots.toFinset with hSdef
  have hS : ∀ z, ratOrder a z < 0 → z ∈ S := fun z hz =>
    Multiset.mem_toFinset.mpr ((mem_roots (RatFunc.denom_ne_zero a)).mpr
      (ratOrder_neg_iff_denom_isRoot hz))
  have hpolar := eq_sum_polar S hS hfin hinf
  choose q hq using fun z : K => hres (some z)
  have hq' : ∀ z, ratResidue a z = q z := fun z => by
    have := hq z
    rwa [connAt_some] at this
  set N := ∏ z ∈ S, (q z).den with hNdef
  have hN : 0 < N := Finset.prod_pos fun z _ => (q z).den_pos
  set n : K → ℤ := fun z => (q z).num * ∏ w ∈ S.erase z, ((q w).den : ℤ) with hndef
  have hn : ∀ z ∈ S, (N : K) * ratResidue a z = n z := by
    intro z hz
    rw [hq' z]
    have hQ : (N : ℚ) * q z = n z := by
      rw [hNdef, hndef]
      push_cast
      rw [← Finset.mul_prod_erase S (fun w => ((q w).den : ℚ)) hz, ← Rat.mul_den_eq_num]
      ring
    have := congrArg (Rat.cast : ℚ → K) hQ
    push_cast at this
    exact this
  refine ⟨N, hN, ∏ z ∈ S, ratLinFac z ^ n z,
    Finset.prod_ne_zero_iff.mpr fun w _ => zpow_ne_zero _ (ratLinFac_ne_zero w), ?_⟩
  rw [logDerivRat_prod_linFac, hpolar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [← mul_assoc]
  congr 1
  rw [show (N : RatFunc K) = RatFunc.C (N : K) by simp, ← map_mul, hn z hz]
  simp

omit [IsAlgClosed K] in
theorem logDerivRat_pow {g : RatFunc K} (hg : g ≠ 0) (N : ℕ) :
    logDerivRat (g ^ N) = (N : RatFunc K) * logDerivRat g := by
  induction N with
  | zero => rw [pow_zero, logDerivRat_one]; simp
  | succ N ih =>
      rw [pow_succ, logDerivRat_mul (pow_ne_zero _ hg) hg, ih]
      push_cast
      ring

/-- A rational function with vanishing logarithmic derivative is a nonzero constant. -/
theorem eq_C_of_logDerivRat_eq_zero {h : RatFunc K} (h0 : h ≠ 0) (hL : logDerivRat h = 0) :
    ∃ κ : K, κ ≠ 0 ∧ h = RatFunc.C κ :=
  eq_C_of_ratOrder_eq_zero_algClosed h0 fun z => by
    obtain ⟨-, hres⟩ := logDerivRat_residue h0 z
    rw [hL, ratResidue_eq_zero_of_regular (by rw [ratOrder_zero])] at hres
    exact_mod_cast hres.symm

/-- **The logarithmic derivative integrates to a cocycle up to a constant.** -/
theorem exists_const_of_logDeriv (hR : ¬ ∃ c : K, R = RatFunc.C c) {a : RatFunc K}
    (ha : connPull R hR a = a) {N : ℕ} {g : RatFunc K} (hg : g ≠ 0)
    (hga : (N : RatFunc K) * a = logDerivRat g) :
    ∃ κ : K, κ ≠ 0 ∧
      g = RatFunc.C κ * (ratFuncSubstitutionAlgHom R hR g * ratFuncDeriv R ^ N) := by
  have hsg : ratFuncSubstitutionAlgHom R hR g ≠ 0 := by
    intro h
    exact hg ((ratFuncSubstitutionAlgHom R hR).toRingHom.injective (by simpa using h))
  have hR' : ratFuncDeriv R ≠ 0 := ratFuncDeriv_ne_zero_of_nonconst' hR
  have hG : ratFuncSubstitutionAlgHom R hR g * ratFuncDeriv R ^ N ≠ 0 :=
    mul_ne_zero hsg (pow_ne_zero _ hR')
  have hLG : logDerivRat (ratFuncSubstitutionAlgHom R hR g * ratFuncDeriv R ^ N)
      = logDerivRat g := by
    rw [logDerivRat_mul hsg (pow_ne_zero _ hR'), logDerivRat_subst, logDerivRat_pow hR', ← hga,
      map_mul, map_natCast]
    conv_rhs => rw [← ha, connPull]
    ring
  obtain ⟨κ, hκ, hκeq⟩ := eq_C_of_logDerivRat_eq_zero (div_ne_zero hg hG) (by
    rw [div_eq_mul_inv, logDerivRat_mul hg (inv_ne_zero hG), logDerivRat_inv hG, hLG,
      add_neg_cancel])
  refine ⟨κ, hκ, ?_⟩
  rw [← hκeq]
  field_simp

omit [CharZero K] [IsAlgClosed K] in
theorem ratValue_pow_of_regular {f : RatFunc K} {z : K} (hf : 0 ≤ ratOrder f z) (n : ℕ) :
    0 ≤ ratOrder (f ^ n) z ∧ ratValue (f ^ n) z = ratValue f z ^ n := by
  induction n with
  | zero => exact ⟨by rw [pow_zero, ratOrder_one], by rw [pow_zero, pow_zero, ratValue_one]⟩
  | succ n ih =>
      refine ⟨by rw [pow_succ]; exact ratOrder_mul_nonneg ih.1 hf, ?_⟩
      rw [pow_succ, ratValue_mul ih.1 hf, ih.2, pow_succ]

omit [CharZero K] [IsAlgClosed K] in
theorem ratValue_zpow_of_unit {f : RatFunc K} {z : K} (hf0 : f ≠ 0) (hf : ratOrder f z = 0)
    (m : ℤ) : ratOrder (f ^ m) z = 0 ∧ ratValue (f ^ m) z = ratValue f z ^ m := by
  have hpow : ∀ n : ℕ, ratOrder (f ^ n) z = 0 ∧ ratValue (f ^ n) z = ratValue f z ^ n := by
    intro n
    refine ⟨by rw [ratOrder_pow hf0, hf, mul_zero], (ratValue_pow_of_regular hf.symm.le n).2⟩
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast]; exact hpow n
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    refine ⟨by rw [ratOrder_inv (pow_ne_zero _ hf0), (hpow n).1, neg_zero], ?_⟩
    rw [ratValue_inv (pow_ne_zero _ hf0) (hpow n).1, (hpow n).2]

omit [IsAlgClosed K] in
/-- **The constant of the cocycle at a fixed point.**  If `R(0) = 0` with multiplier `λ ≠ 0` and
`g = κ·g(R)·R'^N`, then `κ·λ^{m+N} = 1` with `m = ord₀ g`. -/
theorem const_mul_pow_eq_one_at_fixed_point (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0) (hlam : ratValue (ratFuncDeriv R) 0 ≠ 0)
    {N : ℕ} {g : RatFunc K} (hg : g ≠ 0) {κ : K}
    (hκ : g = RatFunc.C κ * (ratFuncSubstitutionAlgHom R hR g * ratFuncDeriv R ^ N)) :
    κ * ratValue (ratFuncDeriv R) 0 ^ (ratOrder g 0 + N) = 1 := by
  set lam := ratValue (ratFuncDeriv R) 0 with hlamdef
  have hR0' : R ≠ 0 := fun h => hR ⟨0, by rw [h, map_zero]⟩
  have hR' : ratFuncDeriv R ≠ 0 := ratFuncDeriv_ne_zero_of_nonconst' hR
  have hR'reg : 0 ≤ ratOrder (ratFuncDeriv R) 0 := ratOrder_deriv_nonneg h0
  have hR'ord : ratOrder (ratFuncDeriv R) 0 = 0 := by
    by_contra hne
    exact hlam ((ratValue_eq_zero_iff hR' hR'reg).mpr (lt_of_le_of_ne hR'reg (Ne.symm hne)))
  have hRord : ratOrder R 0 = 1 := by
    have := ratOrder_ratFuncDeriv_map hR h0
    rw [hR0, map_zero, sub_zero, hR'ord] at this
    omega
  have hX0 : (RatFunc.X : RatFunc K) ≠ 0 := X_ne_zero'
  have hXord : ratOrder (RatFunc.X : RatFunc K) 0 = 1 := by
    simpa using ratOrder_X_pow_zero (K := K) 1
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : RatFunc K, R₁ = R * RatFunc.X⁻¹ := ⟨_, rfl⟩
  have hR₁0 : R₁ ≠ 0 := by rw [hR₁]; exact mul_ne_zero hR0' (inv_ne_zero hX0)
  have hR₁ord : ratOrder R₁ 0 = 0 := by
    rw [hR₁, ratOrder_mul hR0' (inv_ne_zero hX0), ratOrder_inv hX0, hRord, hXord]
    rfl
  have hReq : R = RatFunc.X * R₁ := by rw [hR₁]; field_simp
  have hR₁val : ratValue R₁ 0 = lam := by
    have hderiv : ratFuncDeriv R = R₁ + RatFunc.X * ratFuncDeriv R₁ := by
      rw [hReq, ratFuncDeriv_mul, ratFuncDeriv_X]
      ring
    have hR₁reg : 0 ≤ ratOrder R₁ 0 := hR₁ord.symm.le
    have hr2 : 0 ≤ ratOrder (RatFunc.X * ratFuncDeriv R₁) 0 :=
      ratOrder_mul_nonneg (ratOrder_X_nonneg 0) (ratOrder_deriv_nonneg hR₁reg)
    rw [hlamdef, hderiv, ratValue_add hR₁reg hr2,
      ratValue_mul (ratOrder_X_nonneg 0) (ratOrder_deriv_nonneg hR₁reg), ratValue_X, zero_mul,
      add_zero]
  set m := ratOrder g 0 with hm
  obtain ⟨h, hh⟩ : ∃ h : RatFunc K, h = g * RatFunc.X ^ (-m) := ⟨_, rfl⟩
  have hh0 : h ≠ 0 := by rw [hh]; exact mul_ne_zero hg (zpow_ne_zero _ hX0)
  have hhord : ratOrder h 0 = 0 := by
    rw [hh, ratOrder_mul hg (zpow_ne_zero _ hX0), ratOrder_zpow hX0, hXord]
    ring
  have hgeq : g = RatFunc.X ^ m * h := by
    rw [hh, ← mul_assoc, mul_comm (RatFunc.X ^ m), mul_assoc, ← zpow_add₀ hX0, add_neg_cancel,
      zpow_zero, mul_one]
  have hsubst : ratFuncSubstitutionAlgHom R hR g
      = RatFunc.X ^ m * (R₁ ^ m * ratFuncSubstitutionAlgHom R hR h) := by
    conv_lhs => rw [hgeq]
    rw [map_mul, map_zpow₀, ratFuncSubstitutionAlgHom_X,
      show R ^ m = (RatFunc.X * R₁) ^ m by rw [← hReq], mul_zpow]
    ring
  have key :
      h = RatFunc.C κ * (R₁ ^ m * ratFuncSubstitutionAlgHom R hR h * ratFuncDeriv R ^ N) := by
    have h2 := hκ
    rw [hsubst] at h2
    conv_lhs at h2 => rw [hgeq]
    refine mul_left_cancel₀ (zpow_ne_zero m hX0) ?_
    rw [h2]
    ring
  have hsh := ratValue_ratFuncSubstitution hR h0 (f := h) (by rw [hR0, hhord])
  rw [hR0] at hsh
  obtain ⟨hR₁m, hR₁mval⟩ := ratValue_zpow_of_unit hR₁0 hR₁ord m
  obtain ⟨hR'N, hR'Nval⟩ := ratValue_pow_of_regular hR'reg N
  have hprod1 : 0 ≤ ratOrder (R₁ ^ m * ratFuncSubstitutionAlgHom R hR h) 0 :=
    ratOrder_mul_nonneg hR₁m.symm.le hsh.1
  have hval := congrArg (fun f => ratValue f 0) key
  rw [ratValue_mul (ratOrder_C_nonneg κ 0) (ratOrder_mul_nonneg hprod1 hR'N), ratValue_C,
    ratValue_mul hprod1 hR'N, ratValue_mul hR₁m.symm.le hsh.1, hR₁mval, hsh.2, hR'Nval,
    hR₁val] at hval
  have hv0 : ratValue h 0 ≠ 0 := ratValue_ne_zero_of_unit hh0 hhord
  have hlam0 : lam ≠ 0 := hlam
  rw [zpow_add₀ hlam0, zpow_natCast]
  have : ratValue h 0 * (κ * (lam ^ m * lam ^ N)) = ratValue h 0 * 1 := by
    rw [mul_one]
    nth_rewrite 2 [hval]
    ring
  exact mul_left_cancel₀ hv0 this

/-- **An invariant affine connection yields a rational cocycle.**  If `R` has degree at least two
and a fixed point `0` with multiplier `λ ≠ 0`, and `R^*a = a`, then some `B ≠ 0` satisfies
`R'^N·B = λ^{N+j}·B(R)` with `N ≥ 1`. -/
theorem ratCocycle_of_invariant_connection (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hlam : ratValue (ratFuncDeriv R) 0 ≠ 0) {a : RatFunc K} (ha : connPull R hR a = a) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ B : RatFunc K, B ≠ 0 ∧
      ratFuncDeriv R ^ N * B
        = RatFunc.C (ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + j))
          * ratFuncSubstitutionAlgHom R hR B := by
  obtain ⟨N, hN, g, hg, hga⟩ := exists_logDeriv_of_invariant_connection hR hd ha
  obtain ⟨κ, hκ0, hκ⟩ := exists_const_of_logDeriv hR ha hg hga
  have hone := const_mul_pow_eq_one_at_fixed_point hR h0 hR0 hlam hg hκ
  refine ⟨N, hN, ratOrder g 0, g⁻¹, inv_ne_zero hg, ?_⟩
  have hsg : ratFuncSubstitutionAlgHom R hR g ≠ 0 := by
    intro h
    exact hg ((ratFuncSubstitutionAlgHom R hR).toRingHom.injective (by simpa using h))
  have hR' : ratFuncDeriv R ≠ 0 := ratFuncDeriv_ne_zero_of_nonconst' hR
  have hlamκ : ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + ratOrder g 0) = κ⁻¹ := by
    rw [add_comm]
    exact eq_inv_of_mul_eq_one_right hone
  rw [hlamκ, map_inv₀, map_inv₀]
  conv_lhs => rw [hκ]
  have hC : RatFunc.C κ ≠ 0 := by simpa using hκ0
  field_simp

end

end GaloisForLFunctions.HTGeometry
