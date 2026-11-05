import GaloisForLFunctions.FiniteFreeProbability.NonRealRootCount
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeHardyTheorem
import GaloisForLFunctions.FiniteFreeProbability.HurwitzDeflation
import GaloisForLFunctions.RHTower.XiWindowNonrealBudget

/-!
# The non-real Jensen count converges to the number of off-line zeros

`N_d = #{non-real roots of R_d(Ξ)}`, with multiplicity. **Theorem.** `N_d` increases to the number of non-real
zeros of `Ξ`, with multiplicity, in `ℕ ∪ {∞}`:

* `N_d ≤ Z_c(Ξ)` for every `d`: on-line zeros never create a non-real root;
* if `Z_c(Ξ) < ∞`, then `N_d = Z_c(Ξ)` for all large `d`;
* if `Z_c(Ξ) = ∞`, then `N_d → ∞`.

So `Ξ` has at most `m` off-line zeros iff `N_d ≤ m` for every `d`, iff `N_d ≤ m` for infinitely many `d`; `m = 0`
is RH, and boundedness of `N_d` is the finiteness of the off-line zeros.

**Upper bound (Hermite–Poulain).** For a real polynomial `P` with `P(0) ≠ 0`, `Z_c(P(D)X^d) ≤ Z_c(P)`. Write `P = r q`
with `r` real-rooted and `q` without real roots. The polynomial `q(D)X^d` has degree `d` and is divisible by
`X^{d − deg q}`, so it has at most `deg q = Z_c(P)` non-real roots. Each factor `D − ρ`, `ρ ≠ 0`, of `r(D)` is a
multiple of `1 − D/ρ`, which by Rolle creates no non-real root. Then let `P` run through the real polynomials
approximating `Ξ`, whose non-real roots are off-line zeros of `Ξ`.

**Lower bound.** The rescaled polynomials `Φ_d(u) = Π_x (1 − (x/d)u)` have the same number of non-real roots as `R_d`
and converge to `Ξ`; the corpus theorem that `Ξ` is a window limit of real polynomials with at most `m` non-real
roots only if it has at most `m` non-real zeros concludes.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn RHTower.WindowNonrealBudget

namespace FiniteFreeProbability

noncomputable section

/-! ## Hermite–Poulain -/

theorem nonrealRootCount_C_mul {a : ℝ} (ha : a ≠ 0) (p : ℝ[X]) :
    nonrealRootCount (C a * p) = nonrealRootCount p := by
  rw [nonrealRootCount, nonrealRootCount, natDegree_C_mul ha, roots_C_mul _ ha]

theorem diffOp_X_sub_C (ρ : ℝ) (p : ℝ[X]) : diffOp (X - C ρ) p = derivative p - C ρ * p := by
  simp [diffOp, smul_eq_C_mul]

/-- The first order operator `D − ρ`, `ρ ≠ 0`, keeps the degree and creates no non-real root. -/
theorem diffOp_X_sub_C_count {ρ : ℝ} (hρ : ρ ≠ 0) (p : ℝ[X]) :
    (diffOp (X - C ρ) p).natDegree = p.natDegree ∧
      nonrealRootCount (diffOp (X - C ρ) p) ≤ nonrealRootCount p := by
  have hc : (1 / ρ) ≠ 0 := one_div_ne_zero hρ
  have e : diffOp (X - C ρ) p = C (-ρ) * (p - C (1 / ρ) * derivative p) := by
    rw [diffOp_X_sub_C, mul_sub, ← mul_assoc, ← C_mul, C_neg, show -ρ * (1 / ρ) = -1 by field_simp]
    simp only [C_neg, C_1]
    ring
  have hρ' : -ρ ≠ 0 := neg_ne_zero.2 hρ
  rw [e, natDegree_C_mul hρ', natDegree_sub_C_mul_derivative, nonrealRootCount_C_mul hρ']
  refine ⟨rfl, ?_⟩
  have h := card_roots_le_sub_C_mul_derivative p hc
  rw [nonrealRootCount, nonrealRootCount, natDegree_sub_C_mul_derivative]
  omega

theorem diffOp_prod_count (s : Multiset ℝ) (hs : ∀ ρ ∈ s, ρ ≠ 0) (p : ℝ[X]) :
    (diffOp (s.map fun ρ => X - C ρ).prod p).natDegree = p.natDegree ∧
      nonrealRootCount (diffOp (s.map fun ρ => X - C ρ).prod p) ≤ nonrealRootCount p := by
  induction s using Multiset.induction_on with
  | empty => simp [diffOp]
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun ρ hρ => hs ρ (Multiset.mem_cons_of_mem hρ)
    rw [Multiset.map_cons, Multiset.prod_cons, diffOp_mul]
    obtain ⟨h3, h4⟩ := diffOp_X_sub_C_count (hs a (Multiset.mem_cons_self a s))
      (diffOp (s.map fun ρ => X - C ρ).prod p)
    exact ⟨h3.trans h1, h4.trans h2⟩

/-- **Hermite–Poulain**: a real-rooted symbol with `r(0) ≠ 0` keeps the degree and creates no non-real root. -/
theorem diffOp_splits_count {r : ℝ[X]} (hr : r.Splits) (h0 : r.eval 0 ≠ 0) (p : ℝ[X]) :
    (diffOp r p).natDegree = p.natDegree ∧ nonrealRootCount (diffOp r p) ≤ nonrealRootCount p := by
  have hr0 : r ≠ 0 := fun h => h0 (by rw [h, eval_zero])
  have hlc : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hr0
  have hs : ∀ ρ ∈ r.roots, ρ ≠ 0 := fun ρ hρ h => by
    subst h
    exact h0 ((mem_roots hr0).1 hρ)
  obtain ⟨h1, h2⟩ := diffOp_prod_count r.roots hs p
  rw [hr.eq_prod_roots, diffOp_C_mul_left, natDegree_C_mul hlc, nonrealRootCount_C_mul hlc]
  exact ⟨h1, h2⟩

theorem coeff_diffOp_X_pow {K : Type*} [Field K] (h : K[X]) {d j : ℕ} (hj : j ≤ d) :
    (diffOp h (X ^ d)).coeff j = h.coeff (d - j) * (d.descFactorial (d - j) : K) := by
  rw [diffOp_X_pow, finsetSum_coeff, Finset.sum_eq_single (d - j)]
  · rw [coeff_C_mul_X_pow, if_pos (by omega)]
  · intro i hi hij
    rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
  · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'

/-- `q(D)X^d` has at most `deg q` non-real roots: it is divisible by `X^{d − deg q}`. -/
theorem nonrealRootCount_diffOp_X_pow_le {q : ℝ[X]} (h0 : q.coeff 0 ≠ 0) (d : ℕ) :
    (diffOp q (X ^ d)).natDegree = d ∧ nonrealRootCount (diffOp q (X ^ d)) ≤ q.natDegree := by
  set p := diffOp q (X ^ d) with hp
  have hcoeff : p.coeff d = q.coeff 0 := by
    rw [hp, coeff_diffOp_X_pow q le_rfl]
    simp
  have hdeg : p.natDegree = d :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d))
      (by rwa [hcoeff])
  refine ⟨hdeg, ?_⟩
  have hp0 : p ≠ 0 := fun h => h0 (by rw [← hcoeff, h, coeff_zero])
  rw [nonrealRootCount, hdeg]
  have hdvd : X ^ (d - q.natDegree) ∣ p := by
    rw [hp, diffOp_X_pow]
    refine Finset.dvd_sum fun i _ => ?_
    by_cases hi : i ≤ q.natDegree
    · exact (pow_dvd_pow _ (by omega)).trans (dvd_mul_left _ _)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, C_0, zero_mul]
      exact dvd_zero _
  have hmul : d - q.natDegree ≤ p.rootMultiplicity 0 := by
    rw [le_rootMultiplicity_iff hp0]
    simpa using hdvd
  have hcount : p.rootMultiplicity 0 ≤ Multiset.card p.roots := by
    rw [← count_roots]
    exact Multiset.count_le_card _ _
  omega

/-- **The Jensen polynomials of a real polynomial have no more non-real roots than the polynomial.** -/
theorem nonrealRootCount_diffOp_X_pow_le_self {P : ℝ[X]} (h0 : P.eval 0 ≠ 0) (d : ℕ) :
    nonrealRootCount (diffOp P (X ^ d)) ≤ nonrealRootCount P := by
  have hP : P ≠ 0 := fun h => h0 (by rw [h, eval_zero])
  obtain ⟨r, q, hr, -, -, hrq, hq⟩ := exists_splits_mul_noRealRoots hP
  have h00 : r.eval 0 * q.eval 0 ≠ 0 := by rwa [← eval_mul, ← hrq]
  have hq0 : q.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact right_ne_zero_of_mul h00
  rw [hrq, diffOp_mul, ← hrq]
  exact (diffOp_splits_count hr (left_ne_zero_of_mul h00) _).2.trans
    ((nonrealRootCount_diffOp_X_pow_le hq0 d).2.trans_eq hq)

/-! ## Passage to the limit -/

theorem tendstoLocallyUniformly_eval_of_coeff {P : ℕ → ℂ[X]} {L : ℂ[X]} {D : ℕ}
    (hP : ∀ n, (P n).natDegree ≤ D) (hL : L.natDegree ≤ D)
    (hc : ∀ j, Tendsto (fun n => (P n).coeff j) atTop (𝓝 (L.coeff j))) :
    TendstoLocallyUniformly (fun n z => (P n).eval z) (fun z => L.eval z) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hKR : ∀ u ∈ K, ‖u‖ ≤ R := fun u hu => by
    have := hR₀ hu
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsum : Tendsto (fun n => ∑ j ∈ Finset.range (D + 1), ‖(P n).coeff j - L.coeff j‖ * R ^ j) atTop
      (𝓝 (∑ j ∈ Finset.range (D + 1), ‖L.coeff j - L.coeff j‖ * R ^ j)) :=
    tendsto_finsetSum _ fun j _ => (((hc j).sub tendsto_const_nhds).norm).mul_const _
  simp only [sub_self, norm_zero, zero_mul, Finset.sum_const_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm, eval_eq_sum_range' (Nat.lt_succ_of_le (hP n)),
    eval_eq_sum_range' (Nat.lt_succ_of_le hL), ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (Finset.sum_le_sum fun j _ => ?_) hn)
  rw [← sub_mul, norm_mul, norm_pow]
  gcongr
  exact hKR z hz

/-- Non-real roots persist: the non-real count is lower semicontinuous under locally uniform limits. -/
theorem nonrealRootCount_le_of_tendsto {S : ℕ → ℝ[X]} {L : ℝ[X]} (hL : L ≠ 0) (hS : ∀ n, S n ≠ 0) {K : ℕ}
    (hK : ∀ n, nonrealRootCount (S n) ≤ K)
    (hconv : TendstoLocallyUniformly (fun n z => ((S n).map Complex.ofRealHom).eval z)
      (fun z => (L.map Complex.ofRealHom).eval z) atTop) :
    nonrealRootCount L ≤ K := by
  classical
  set B := L.map Complex.ofRealHom
  have hB : B ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hL
  obtain ⟨r, hr⟩ := exists_isolating_discs hB
  set T := (B.roots.filter (fun z => z.im ≠ 0)).toFinset
  set F : ℕ → ℂ → ℂ := fun n z => ((S n).map Complex.ofRealHom).eval z
  have hFd : ∀ n, Differentiable ℂ (F n) := fun n => Polynomial.differentiable _
  have hev : ∀ e ∈ T, ∀ᶠ n in atTop,
      zeroSumBall (F n) e (r e) = (B.rootMultiplicity e : ℂ) ∧
        ∀ w ∈ sphere e (r e), F n w ≠ 0 := by
    intro e he
    obtain ⟨hr0, -, -, hsph, hcount⟩ := hr e he
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hFd B.differentiable hconv hr0
      (by linarith : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere B.continuous hconv hr0.le hsph
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  obtain ⟨n, hnT⟩ := ((Filter.eventually_all_finset T).mpr hev).exists
  have hBA : (S n).map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr (hS n)
  have hsum := sum_le_card_nonreal_roots hBA (E := T) (r := r)
    (n := fun e => B.rootMultiplicity e)
    (fun e he => (hr e he).1) (fun e he => (hr e he).2.1) (fun e he => (hr e he).2.2.1)
    (fun e he => (hnT e he).2) (fun e he => (hnT e he).1)
  rw [nonrealRootCount_eq L, card_filter_roots_eq_sum]
  rw [← nonrealRootCount_eq (S n)] at hsum
  exact hsum.trans (hK n)

/-! ## The non-real Jensen count -/

/-- `N_d`: the number of non-real roots of `R_d(Ξ)`, with multiplicity. -/
def jensenNonrealCount (d : ℕ) : ℕ :=
  Multiset.card ((jensenRev d xiSeries).roots.filter fun z => z.im ≠ 0)

theorem jensenNonrealCount_eq (d : ℕ) : jensenNonrealCount d = nonrealRootCount (xiJensenReal d) := by
  rw [nonrealRootCount_eq, jensenNonrealCount, jensenRev_xiSeries]
  rfl

theorem jensenNonrealCount_mono : Monotone jensenNonrealCount :=
  monotone_nat_of_le_succ card_nonreal_roots_le_succ

theorem xiJensenReal_ne_zero (d : ℕ) : xiJensenReal d ≠ 0 := fun h => by
  have := natDegree_xiJensenReal d
  rw [h, natDegree_zero] at this
  have hc := constantCoeff_mk_realTaylorCoeff
  have hco : (xiJensenReal d).coeff d ≠ 0 := by
    rw [xiJensenReal_eq, coeff_jensenRev_self]
    exact hc
  exact hco (by rw [h, coeff_zero])

theorem eval_zero_xiRealApprox (n : ℕ) : (xiRealApprox n).eval 0 ≠ 0 := by
  intro h
  have h1 := eval_map_xiRealApprox n 0
  have h2 : ((xiRealApprox n).map Complex.ofRealHom).eval 0 = 0 := by
    have := eval_map_apply (p := xiRealApprox n) (f := Complex.ofRealHom) (0 : ℝ)
    rw [h, map_zero] at this
    simpa using this
  rw [h2] at h1
  have h3 := map_xiRealApprox n
  have h4 := congrArg (eval 0) h3
  rw [h2, eval_mul, eval_C, eval_xiZeroPoly] at h4
  simp only [zero_div, sub_zero, Finset.prod_const_one, mul_one] at h4
  exact DeBruijn.XiC_zero_ne_zero h4.symm

/-- The coefficients of the real approximants converge to the Taylor coefficients of `Ξ`. -/
theorem tendsto_coeff_xiRealApprox (k : ℕ) :
    Tendsto (fun n => (((xiRealApprox n).coeff k : ℝ) : ℂ)) atTop
      (𝓝 ((realTaylorCoeff XiC k : ℝ) : ℂ)) := by
  have hloc := tendstoLocallyUniformly_xiRealApprox
  rw [DeBruijn.riemannHeat_zero_eq_XiC] at hloc
  have h := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
    (tendstoLocallyUniformlyOn_univ.2 hloc)
    (Eventually.of_forall fun n => (Polynomial.differentiable _).differentiableOn) k (Set.mem_univ 0)
  have hk : ((k.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 := h.const_mul ((k.factorial : ℂ))⁻¹
  rw [← ofReal_realTaylorCoeff (fun w => XiC_conj w)] at h2
  refine h2.congr fun n => ?_
  have hcoeff := congrArg (PowerSeries.coeff k)
    (taylorPS_polynomial ((xiRealApprox n).map Complex.ofRealHom))
  rw [taylorPS, PowerSeries.coeff_mk, Polynomial.coeff_coe, coeff_map] at hcoeff
  rw [inv_mul_eq_div, hcoeff]
  rfl

/-- **On-line zeros create no non-real Jensen root**: if `Ξ` has at most `m` non-real zeros, every `R_d(Ξ)` has at
most `m` non-real roots. -/
theorem jensenNonrealCount_le_of_encard {m : ℕ}
    (hm : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m) (d : ℕ) :
    jensenNonrealCount d ≤ m := by
  have hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite :=
    Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.coe_ne_top m) hm)
  have hcard : hfin.toFinset.card ≤ m := by
    rw [hfin.encard_eq_coe_toFinset_card] at hm
    exact_mod_cast hm
  rw [jensenNonrealCount_eq]
  set S : ℕ → ℝ[X] := fun n => diffOp (xiRealApprox n) (X ^ d)
  have hcoeff0 : ∀ n, (xiRealApprox n).coeff 0 ≠ 0 := fun n => by
    rw [coeff_zero_eq_eval_zero]
    exact eval_zero_xiRealApprox n
  have hS : ∀ n, S n ≠ 0 := fun n h => by
    have hco := coeff_diffOp_X_pow (xiRealApprox n) (le_refl d)
    rw [show diffOp (xiRealApprox n) (X ^ d) = S n from rfl, h, coeff_zero] at hco
    simp only [Nat.sub_self, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hco
    exact hcoeff0 n hco.symm
  have hSdeg : ∀ n, (S n).natDegree ≤ d := fun n =>
    (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  refine nonrealRootCount_le_of_tendsto (xiJensenReal_ne_zero d) hS (fun n => ?_) ?_
  · exact (nonrealRootCount_diffOp_X_pow_le_self (eval_zero_xiRealApprox n) d).trans
      ((nonrealRootCount_xiRealApprox_le hfin n).trans hcard)
  · refine tendstoLocallyUniformly_eval_of_coeff (D := d)
      (fun n => natDegree_map_le.trans (hSdeg n))
      (natDegree_map_le.trans (natDegree_xiJensenReal d).le) fun j => ?_
    simp only [coeff_map]
    rcases le_or_gt j d with hj | hj
    · have hL : (xiJensenReal d).coeff j =
          realTaylorCoeff XiC (d - j) * (d.descFactorial (d - j) : ℝ) := by
        rw [xiJensenReal_eq, jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single (d - j)]
        · rw [coeff_C_mul_X_pow, if_pos (by omega), PowerSeries.coeff_mk]
        · intro i hi hij
          rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
        · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'
      simp only [S, coeff_diffOp_X_pow _ hj, hL, Complex.ofRealHom_eq_coe]
      push_cast
      exact (tendsto_coeff_xiRealApprox (d - j)).mul_const _
    · have h1 : (xiJensenReal d).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_xiJensenReal]; exact hj)
      have h2 : ∀ n, (S n).coeff j = 0 := fun n => coeff_eq_zero_of_natDegree_lt ((hSdeg n).trans_lt hj)
      simp only [h1, h2, map_zero, tendsto_const_nhds_iff]

/-! ## The rescaled approximants -/

/-- The real polynomial `Φ_d`. -/
def xiScaledReal (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (realTaylorCoeff XiC k * ((d.descFactorial k : ℝ) / (d : ℝ) ^ k)) * X ^ k

theorem eval_map_xiScaledReal (d : ℕ) (u : ℂ) :
    ((xiScaledReal d).map Complex.ofRealHom).eval u = scaledJensen xiCoeff d u := by
  simp only [xiScaledReal, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, scaledJensen, xiCoeff, Complex.ofRealHom_eq_coe]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem xiCoeff_zero_ne : xiCoeff 0 ≠ 0 := by
  have h := constantCoeff_mk_realTaylorCoeff
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk] at h
  exact Complex.ofReal_ne_zero.2 h

/-- The multiset of non-real roots of `Π_v (1 − v X)` corresponds to the non-real elements of the multiset. -/
theorem card_filter_roots_linearProd (V : Multiset ℂ) :
    Multiset.card ((V.map fun v => (1 - C v * X : ℂ[X])).prod.roots.filter fun z => z.im ≠ 0) =
      Multiset.card (V.filter fun z => z.im ≠ 0) := by
  have hfactor : ∀ v : ℂ, (1 - C v * X : ℂ[X]) ≠ 0 := fun v h => by
    have := congrArg (eval 0) h
    simp at this
  induction V using Multiset.induction_on with
  | empty => simp
  | cons a V ih =>
    have hne : (a : ℂ) = a := rfl
    have hP : (1 - C a * X : ℂ[X]) * (V.map fun v => (1 - C v * X : ℂ[X])).prod ≠ 0 :=
      mul_ne_zero (hfactor a) (Multiset.prod_ne_zero (fun h => by
        obtain ⟨v, _, hv⟩ := Multiset.mem_map.1 h
        exact hfactor v hv))
    rw [Multiset.map_cons, Multiset.prod_cons, roots_mul hP, Multiset.filter_add, Multiset.card_add, ih,
      Multiset.filter_cons, Multiset.card_add]
    congr 1
    by_cases ha : a = 0
    · subst ha
      simp
    · have hroots : (1 - C a * X : ℂ[X]).roots = {a⁻¹} := by
        have hfac : (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
          rw [C_neg, neg_mul, mul_sub, ← C_mul, mul_inv_cancel₀ ha, C_1]
          ring
        rw [hfac, roots_C_mul _ (neg_ne_zero.2 ha), roots_X_sub_C]
      have him : (a⁻¹).im ≠ 0 ↔ a.im ≠ 0 := by
        have hns : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
        rw [Complex.inv_im, ne_eq, div_eq_zero_iff, neg_eq_zero, not_or, ne_eq]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, hns.ne'⟩
      rw [hroots, Multiset.filter_singleton]
      by_cases h : a.im ≠ 0
      · simp [ha, h]
      · simp [h]

/-- `Φ_d` has the non-real roots of `R_d`, with multiplicity. -/
theorem nonrealRootCount_xiScaledReal_le {d : ℕ} (hd : 0 < d) :
    nonrealRootCount (xiScaledReal d) ≤ jensenNonrealCount d := by
  have hc := xiCoeff_zero_ne
  set g : ℕ → ℂ := fun k => xiCoeff k / xiCoeff 0 with hg
  have hg0 : g 0 = 1 := div_self hc
  set V := jensenScaledRoots g d
  have hprod : (xiScaledReal d).map Complex.ofRealHom =
      C (xiCoeff 0) * (V.map fun v => (1 - C v * X : ℂ[X])).prod := by
    refine Polynomial.funext fun u => ?_
    have h1 : scaledJensen xiCoeff d u = xiCoeff 0 * scaledJensen g d u := by
      simp only [scaledJensen, Finset.mul_sum, hg]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [eval_map_xiScaledReal, h1, scaledJensen_eq_linearProd hg0 hd, eval_mul, eval_C, linearProd,
      eval_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun v _ => ?_
    simp [mul_comm]
  have hmk : PowerSeries.mk g = PowerSeries.C (xiCoeff 0)⁻¹ * xiSeries := by
    rw [← mk_xiCoeff]
    ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [hg]
    field_simp
  have hroots : (jensenRev d (PowerSeries.mk g)).roots = (jensenRev d xiSeries).roots := by
    rw [hmk, jensenRev_C_mul, roots_C_mul _ (inv_ne_zero hc)]
  rw [nonrealRootCount_eq, hprod, roots_C_mul _ hc, card_filter_roots_linearProd, jensenNonrealCount,
    ← hroots]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have him : ∀ x : ℂ, (x / (d : ℂ)).im ≠ 0 ↔ x.im ≠ 0 := fun x => by
    rw [show x / (d : ℂ) = x * (((d : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_mul_ofReal, ne_eq,
      mul_eq_zero, not_or, ne_eq]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, inv_ne_zero hdR.ne'⟩
  simp only [V, jensenScaledRoots, Multiset.filter_map, Multiset.card_map]
  refine le_of_eq (congrArg _ (Multiset.filter_congr fun x _ => ?_))
  simpa using him x

/-- If `N_d ≤ m` along all large degrees, `Ξ` has at most `m` non-real zeros. -/
theorem encard_le_of_jensenNonrealCount_le {m : ℕ} (hm : ∀ d, jensenNonrealCount d ≤ m) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m := by
  have hsum : ∀ z, HasSum (fun k => xiCoeff k * z ^ k) (XiC z) := fun z => by
    simpa [xiSeries, xiCoeff] using hasSum_xiSeries z
  have hf := summable_norm_mul_pow_of_summable fun z => (hsum z).summable
  have hloc := tendstoLocallyUniformly_scaledJensen hf (ψ := fun n => n + 1) (tendsto_add_atTop_nat 1)
  have hfun : (fun u => ∑' k, xiCoeff k * u ^ k) = XiC := funext fun u => (hsum u).tsum_eq
  rw [hfun] at hloc
  refine encard_nonrealCopies_le_of_window (P := fun n => xiScaledReal (n + 1)) (c := 0) (ε := 1)
    (fun n => (nonrealRootCount_xiScaledReal_le n.succ_pos).trans (hm _)) one_pos ?_
  have hK : IsCompact ((fun t : ℝ => (t : ℂ)) '' Set.Icc ((0 : ℝ) - 1) (0 + 1)) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc) _ hK
  have hu' := (hu.comp (fun t : ℝ => (t : ℂ))).mono (fun t ht => ⟨t, ht, rfl⟩)
  refine hu'.congr (Eventually.of_forall fun n t _ => ?_)
  simp only [Function.comp_apply]
  rw [polyEvalC_eq_eval_map]
  exact (eval_map_xiScaledReal (n + 1) t).symm

/-! ## The theorem -/

/-- **`Ξ` has at most `m` off-line zeros iff every `R_d(Ξ)` has at most `m` non-real roots.** -/
theorem encard_offLine_le_iff_forall {m : ℕ} :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m ↔ ∀ d, jensenNonrealCount d ≤ m :=
  ⟨jensenNonrealCount_le_of_encard, encard_le_of_jensenNonrealCount_le⟩

/-- A bound at infinitely many degrees is a bound at every degree. -/
theorem encard_offLine_le_iff_frequently {m : ℕ} :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m ↔
      ∃ᶠ d in atTop, jensenNonrealCount d ≤ m := by
  rw [encard_offLine_le_iff_forall]
  constructor
  · intro h
    exact Eventually.frequently (Eventually.of_forall h)
  · intro h d
    obtain ⟨e, he, hem⟩ := (h.and_eventually (eventually_ge_atTop d)).exists
    exact (jensenNonrealCount_mono hem).trans he

/-- **`N_d` converges to the off-line zero count.** If the off-line zeros are finitely many, `N_d` equals their
number, with multiplicity, for all large `d`. -/
theorem eventually_jensenNonrealCount_eq_of_finite
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    ∀ᶠ d in atTop, jensenNonrealCount d = hfin.toFinset.card := by
  set K := hfin.toFinset.card with hK
  have hle : ∀ d, jensenNonrealCount d ≤ K :=
    jensenNonrealCount_le_of_encard (by rw [hfin.encard_eq_coe_toFinset_card])
  have hex : ∃ d, K ≤ jensenNonrealCount d := by
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · exact absurd (hcon 0) (by omega)
    · have h1 : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ ((K - 1 : ℕ) : ℕ∞) :=
        encard_le_of_jensenNonrealCount_le fun d => by have := hcon d; omega
      rw [hfin.encard_eq_coe_toFinset_card] at h1
      have h2 : K ≤ K - 1 := by exact_mod_cast h1
      omega
  obtain ⟨d₀, hd₀⟩ := hex
  filter_upwards [eventually_ge_atTop d₀] with d hd
  exact le_antisymm (hle d) (hd₀.trans (jensenNonrealCount_mono hd))

/-- If `Ξ` has infinitely many off-line zeros, `N_d → ∞`. -/
theorem tendsto_jensenNonrealCount_of_infinite
    (hinf : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite) :
    Tendsto jensenNonrealCount atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone jensenNonrealCount_mono fun M => ?_
  by_contra hcon
  push Not at hcon
  have h1 : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ M :=
    encard_le_of_jensenNonrealCount_le fun d => (hcon d).le
  exact hinf (Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.coe_ne_top M) h1))

/-- **The supremum of the non-real Jensen count is the number of off-line zeros.** -/
theorem iSup_jensenNonrealCount :
    (⨆ d, (jensenNonrealCount d : ℕ∞)) = {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard := by
  by_cases hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite
  · rw [hfin.encard_eq_coe_toFinset_card]
    refine le_antisymm (iSup_le fun d => ?_) ?_
    · exact_mod_cast jensenNonrealCount_le_of_encard
        (by rw [hfin.encard_eq_coe_toFinset_card]) d
    · obtain ⟨d, hd⟩ := (eventually_jensenNonrealCount_eq_of_finite hfin).exists
      rw [← hd]
      exact le_iSup (fun d => (jensenNonrealCount d : ℕ∞)) d
  · have htop : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard = ⊤ :=
      Set.encard_eq_top_iff.2 hfin
    rw [htop, eq_top_iff]
    refine ENat.forall_natCast_le_iff_le.1 fun M _ => ?_
    obtain ⟨d, hd⟩ := ((tendsto_jensenNonrealCount_of_infinite hfin).eventually_ge_atTop M).exists
    exact (by exact_mod_cast hd : (M : ℕ∞) ≤ jensenNonrealCount d).trans
      (le_iSup (fun d => (jensenNonrealCount d : ℕ∞)) d)

/-- `N_d` is bounded iff `Ξ` has finitely many off-line zeros, iff the non-real counts `N(t)` of the de Bruijn–Newman
flow are bounded as `t → 0⁺`. -/
theorem bddAbove_jensenNonrealCount_iff :
    (∃ M, ∀ d, jensenNonrealCount d ≤ M) ↔
      {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite := by
  rw [finite_nonreal_zeros_iff_exists_nonrealZeroCount_le]
  constructor
  · rintro ⟨M, hM⟩
    have h1 := encard_le_of_jensenNonrealCount_le hM
    have hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite :=
      Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.coe_ne_top M) h1)
    exact ⟨hfin.toFinset.card, fun t ht => nonrealZeroCount_le_of_finite_nonreal_zeros hfin ht⟩
  · intro h
    have hZ := finite_nonreal_zeros_iff_exists_nonrealZeroCount_le.2 h
    have hfin := finite_nonrealCopies_of_finite_zeros hZ
    exact ⟨hfin.toFinset.card, fun d => jensenNonrealCount_le_of_encard
      (by rw [hfin.encard_eq_coe_toFinset_card]) d⟩

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.encard_offLine_le_iff_forall
#print axioms FiniteFreeProbability.encard_offLine_le_iff_frequently
#print axioms FiniteFreeProbability.eventually_jensenNonrealCount_eq_of_finite
#print axioms FiniteFreeProbability.tendsto_jensenNonrealCount_of_infinite
#print axioms FiniteFreeProbability.iSup_jensenNonrealCount
#print axioms FiniteFreeProbability.bddAbove_jensenNonrealCount_iff
