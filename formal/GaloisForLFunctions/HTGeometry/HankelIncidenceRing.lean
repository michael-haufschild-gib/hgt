import GaloisForLFunctions.HTGeometry.PolynomialTwistedCech
import GaloisForLFunctions.HTGeometry.TriangularVariableElimination
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Ideal

/-!
# The Hankel incidence ring

`T = K[z_0, …, z_r, v_0, …, v_{N-1}]`: the `z_i` are the coefficients of a binary form
`G = ∑ z_i X^i` of degree `≤ r`, the `v_n` are moments.  The *Hankel equations*

`ℓ_j = ∑_i z_i v_{i+j}  (j < N - r)`

say that `G` annihilates the moment sequence; `Proj (T/(ℓ))` is the incidence variety resolving the
`r`-secant variety of the rational normal curve.  Writing `⟨p, v⟩ = ∑_n p_n v_n` for the pairing of
a polynomial with the moments, `ℓ_j = ⟨G X^j, v⟩`.

For `t ∈ K` the *moment shift* `σ_t` substitutes `G ↦ G(X + t)` and `v_n ↦ ⟨(X - t)^n, v⟩`.  It is
an automorphism (with inverse `σ_{-t}`) that sends `z_0 = G(0)` to the chart form `G(t)` and
`ℓ_j` to `⟨G (X - t)^j, v⟩ ∈ ℓ_j + (ℓ_0, …, ℓ_{j-1})`.  This moves every evaluation chart
`G(t) ≠ 0` to the chart `G(0) ≠ 0`, where the equations are triangular in the moments.

* `HTGeometry.hankelEq`, `HTGeometry.hankelIdeal`, `HTGeometry.chartForm`.
* `HTGeometry.momentShift`, `HTGeometry.momentShift_hankelEq`, `HTGeometry.momentShift_neg_comp`.
-/

namespace HTGeometry

open Polynomial

universe u

variable (K : Type u) [Field K] (r N : ℕ)

/-- The incidence ring `K[z_0..z_r, v_0..v_{N-1}]`. -/
abbrev IncRing := MvPolynomial (Fin (r + 1) ⊕ Fin N) K

/-- The coefficients of the binary form. -/
noncomputable def zv (i : Fin (r + 1)) : IncRing K r N := MvPolynomial.X (Sum.inl i)

/-- The moments. -/
noncomputable def vv (n : Fin N) : IncRing K r N := MvPolynomial.X (Sum.inr n)

/-- The universal polynomial `G = ∑ z_i X^i`. -/
noncomputable def gPoly : (IncRing K r N)[X] := ∑ i : Fin (r + 1), C (zv K r N i) * X ^ (i : ℕ)

/-- The pairing `⟨p, v⟩ = ∑_{n < N} p_n v_n` of a polynomial with the moments. -/
noncomputable def momentPair (p : (IncRing K r N)[X]) : IncRing K r N :=
  ∑ n : Fin N, p.coeff n * vv K r N n

/-- **The Hankel equations** `ℓ_j = ⟨G X^j, v⟩ = ∑_i z_i v_{i+j}`. -/
noncomputable def hankelEq (j : ℕ) : IncRing K r N := momentPair K r N (gPoly K r N * X ^ j)

/-- The ideal of the first `j` Hankel equations. -/
noncomputable def hankelIdeal (j : ℕ) : Ideal (IncRing K r N) :=
  Ideal.span (hankelEq K r N '' {m | m < j})

/-- **The evaluation chart form** `G(t)`. -/
noncomputable def chartForm (t : K) : IncRing K r N := (gPoly K r N).eval (algebraMap K _ t)

variable {K r N}

theorem hankelIdeal_mono {j j' : ℕ} (h : j ≤ j') : hankelIdeal K r N j ≤ hankelIdeal K r N j' :=
  Ideal.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)

theorem hankelEq_mem_hankelIdeal {m j : ℕ} (h : m < j) : hankelEq K r N m ∈ hankelIdeal K r N j :=
  Ideal.subset_span ⟨m, h, rfl⟩

theorem hankelIdeal_succ (j : ℕ) :
    hankelIdeal K r N (j + 1) = hankelIdeal K r N j ⊔ Ideal.span {hankelEq K r N j} := by
  rw [hankelIdeal, hankelIdeal, ← Ideal.span_union, ← Set.image_singleton, ← Set.image_union]
  congr 2
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  omega

theorem gPoly_coeff (i : ℕ) :
    (gPoly K r N).coeff i = if h : i < r + 1 then zv K r N ⟨i, h⟩ else 0 := by
  rw [gPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h' => hb (Fin.ext h'.symm)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (fun (h' : i = (b : ℕ)) => h (h' ▸ b.2)), mul_zero]

theorem natDegree_gPoly_le : (gPoly K r N).natDegree ≤ r := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [gPoly_coeff, dif_neg (by omega)]

theorem momentPair_add (p q : (IncRing K r N)[X]) :
    momentPair K r N (p + q) = momentPair K r N p + momentPair K r N q := by
  simp only [momentPair, coeff_add, add_mul, Finset.sum_add_distrib]

theorem momentPair_C_mul (a : IncRing K r N) (p : (IncRing K r N)[X]) :
    momentPair K r N (C a * p) = a * momentPair K r N p := by
  simp only [momentPair, coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem momentPair_sum {α : Type*} (s : Finset α) (f : α → (IncRing K r N)[X]) :
    momentPair K r N (∑ a ∈ s, f a) = ∑ a ∈ s, momentPair K r N (f a) := by
  simp only [momentPair, finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

theorem momentPair_X_pow (n : Fin N) : momentPair K r N (X ^ (n : ℕ)) = vv K r N n := by
  rw [momentPair, Finset.sum_eq_single n]
  · simp
  · intro b _ hb
    rw [coeff_X_pow, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · simp

/-! ## The moment shift -/

variable (K r N) in
/-- **The moment shift** `σ_t`: `G ↦ G(X + t)`, `v_n ↦ ⟨(X - t)^n, v⟩`. -/
noncomputable def momentShift (t : K) : IncRing K r N →ₐ[K] IncRing K r N :=
  MvPolynomial.aeval (Sum.elim
    (fun i => ((gPoly K r N).comp (X + C (algebraMap K _ t))).coeff (i : ℕ))
    (fun n => momentPair K r N ((X - C (algebraMap K _ t)) ^ (n : ℕ))))

theorem momentShift_zv (t : K) (i : Fin (r + 1)) :
    momentShift K r N t (zv K r N i)
      = ((gPoly K r N).comp (X + C (algebraMap K _ t))).coeff (i : ℕ) := by
  simp [momentShift, zv]

theorem momentShift_vv (t : K) (n : Fin N) :
    momentShift K r N t (vv K r N n) = momentPair K r N ((X - C (algebraMap K _ t)) ^ (n : ℕ)) := by
  simp [momentShift, vv]

theorem natDegree_gPoly_comp_le (a : IncRing K r N) :
    ((gPoly K r N).comp (X + C a)).natDegree ≤ r := by
  refine natDegree_comp_le.trans ?_
  have h1 : (X + C a : (IncRing K r N)[X]).natDegree ≤ 1 := natDegree_add_C.le.trans natDegree_X_le
  calc (gPoly K r N).natDegree * (X + C a).natDegree ≤ r * 1 :=
        Nat.mul_le_mul natDegree_gPoly_le h1
    _ = r := mul_one r

/-- **The shift translates `G`.** -/
theorem map_momentShift_gPoly (t : K) :
    (gPoly K r N).map (momentShift K r N t).toRingHom = (gPoly K r N).comp (X + C (algebraMap K _ t)) := by
  refine Polynomial.ext fun i => ?_
  rw [coeff_map, gPoly_coeff]
  split_ifs with h
  · exact momentShift_zv t ⟨i, h⟩
  · rw [map_zero]
    symm
    exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_gPoly_comp_le (K := K) (r := r) (N := N) _).trans_lt (by omega))

/-- **The shift of a pairing.** -/
theorem momentShift_momentPair (t : K) {p : (IncRing K r N)[X]} (hp : p.natDegree < N) :
    momentShift K r N t (momentPair K r N p)
      = momentPair K r N ((p.map (momentShift K r N t).toRingHom).comp
          (X - C (algebraMap K _ t))) := by
  set Y : (IncRing K r N)[X] := X - C (algebraMap K _ t) with hY
  set σ := (momentShift K r N t).toRingHom with hσ
  have hR : momentPair K r N ((p.map σ).comp Y)
      = ∑ n : Fin N, σ (p.coeff n) * momentPair K r N (Y ^ (n : ℕ)) := by
    rw [comp_eq_sum_left,
      Polynomial.sum_over_range' _ (fun _ => by simp) N ((natDegree_map_le).trans_lt hp),
      momentPair_sum, ← Fin.sum_univ_eq_sum_range
        (fun a => momentPair K r N (C ((p.map σ).coeff a) * Y ^ a)) N]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [momentPair_C_mul, coeff_map]
  rw [hR, momentPair, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, momentShift_vv]
  rfl

theorem comp_X_add_C_X_sub_C (a : IncRing K r N) :
    (X + C a : (IncRing K r N)[X]).comp (X - C a) = X := by
  rw [add_comp, X_comp, C_comp, sub_add_cancel]

theorem comp_X_sub_C_X_add_C (a : IncRing K r N) :
    (X - C a : (IncRing K r N)[X]).comp (X + C a) = X := by
  rw [sub_comp, X_comp, C_comp, add_sub_cancel_right]

/-- **The shift of a Hankel equation** is the pairing with `G (X - t)^j`. -/
theorem momentShift_hankelEq (t : K) {j : ℕ} (hj : j + r < N) :
    momentShift K r N t (hankelEq K r N j)
      = momentPair K r N (gPoly K r N * (X - C (algebraMap K _ t)) ^ j) := by
  have hdeg : (gPoly K r N * X ^ j).natDegree < N := by
    refine (natDegree_mul_le).trans_lt ?_
    have := natDegree_gPoly_le (K := K) (r := r) (N := N)
    have h2 : (X ^ j : (IncRing K r N)[X]).natDegree ≤ j := natDegree_X_pow_le j
    omega
  rw [hankelEq, momentShift_momentPair t hdeg, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_momentShift_gPoly, mul_comp, X_pow_comp, comp_assoc, comp_X_add_C_X_sub_C, comp_X]

theorem coeff_X_sub_C_pow_sub_eq_zero (a : IncRing K r N) {j m : ℕ} (hm : j ≤ m) :
    ((X - C a) ^ j - X ^ j : (IncRing K r N)[X]).coeff m = 0 := by
  have hmon : ((X - C a) ^ j : (IncRing K r N)[X]).Monic := (monic_X_sub_C a).pow j
  have hdeg : ((X - C a) ^ j : (IncRing K r N)[X]).natDegree = j := by
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [coeff_sub]
  rcases eq_or_lt_of_le hm with heq | hlt
  · have h1 := hmon.coeff_natDegree
    rw [hdeg] at h1
    rw [← heq, h1, coeff_X_pow_self, sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt), coeff_X_pow, if_neg (by omega),
      sub_zero]

/-- **The shift preserves the Hankel equations modulo the earlier ones.** -/
theorem momentShift_hankelEq_sub_mem (t : K) {j : ℕ} (hj : j + r < N) :
    momentShift K r N t (hankelEq K r N j) - hankelEq K r N j ∈ hankelIdeal K r N j := by
  rw [momentShift_hankelEq t hj, hankelEq]
  set R : (IncRing K r N)[X] := (X - C (algebraMap K _ t)) ^ j - X ^ j with hR
  have hsplit : (X - C (algebraMap K _ t)) ^ j = X ^ j + R := by rw [hR]; ring
  rw [hsplit, mul_add, momentPair_add, add_sub_cancel_left]
  have hRsum : R = ∑ m ∈ R.support, C (R.coeff m) * X ^ m := R.as_sum_support_C_mul_X_pow
  rw [hRsum, Finset.mul_sum, momentPair_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [mul_left_comm, momentPair_C_mul]
  refine Ideal.mul_mem_left _ _ (hankelEq_mem_hankelIdeal ?_)
  by_contra hjm
  exact (mem_support_iff.mp hm) (coeff_X_sub_C_pow_sub_eq_zero _ (not_lt.mp hjm))

/-- The shift of an earlier Hankel equation lies in the ideal. -/
theorem momentShift_hankelEq_mem (t : K) {m j : ℕ} (hm : m < j) (hj : j + r ≤ N) :
    momentShift K r N t (hankelEq K r N m) ∈ hankelIdeal K r N j := by
  have hm' : m + r < N := by omega
  have h1 := hankelIdeal_mono (K := K) (r := r) (N := N) (le_of_lt hm)
    (momentShift_hankelEq_sub_mem t hm')
  rw [← sub_add_cancel (momentShift K r N t (hankelEq K r N m)) (hankelEq K r N m)]
  exact Ideal.add_mem _ h1 (hankelEq_mem_hankelIdeal hm)

/-- **The shift preserves the ideals of the Hankel equations.** -/
theorem momentShift_mem_hankelIdeal (t : K) {j : ℕ} (hj : j + r ≤ N) {x : IncRing K r N}
    (hx : x ∈ hankelIdeal K r N j) : momentShift K r N t x ∈ hankelIdeal K r N j := by
  have hle : hankelIdeal K r N j ≤ (hankelIdeal K r N j).comap (momentShift K r N t) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact momentShift_hankelEq_mem t hm hj
  exact hle hx

/-- **The shift moves the chart `G(0) ≠ 0` to the chart `G(t) ≠ 0`.** -/
theorem momentShift_zv_zero (t : K) : momentShift K r N t (zv K r N 0) = chartForm K r N t := by
  rw [momentShift_zv, Fin.val_zero, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C,
    zero_add, chartForm]

theorem momentShift_algebraMap (t a : K) :
    momentShift K r N t (algebraMap K _ a) = algebraMap K _ a := (momentShift K r N t).commutes a

/-- **`σ_{-t}` inverts `σ_t`.** -/
theorem momentShift_neg_comp (t : K) :
    (momentShift K r N (-t)).comp (momentShift K r N t) = AlgHom.id K _ := by
  have hσ : ∀ s a, (momentShift K r N s).toRingHom a = momentShift K r N s a := fun _ _ => rfl
  have hX : (X + C (algebraMap K (IncRing K r N) t)).map (momentShift K r N (-t)).toRingHom
      = X + C (algebraMap K _ t) := by
    rw [Polynomial.map_add, map_X, map_C, hσ, momentShift_algebraMap]
  apply MvPolynomial.algHom_ext
  rintro (i | n)
  · change momentShift K r N (-t) (momentShift K r N t (zv K r N i)) = zv K r N i
    rw [momentShift_zv]
    change (momentShift K r N (-t)).toRingHom
      (((gPoly K r N).comp (X + C (algebraMap K (IncRing K r N) t))).coeff (i : ℕ)) = zv K r N i
    rw [← coeff_map, Polynomial.map_comp, map_momentShift_gPoly, hX, comp_assoc,
      map_neg, C_neg, ← sub_eq_add_neg, comp_X_sub_C_X_add_C, comp_X, gPoly_coeff, dif_pos i.2]
  · change momentShift K r N (-t) (momentShift K r N t (vv K r N n)) = vv K r N n
    have hdeg : ((X - C (algebraMap K (IncRing K r N) t)) ^ (n : ℕ)).natDegree < N := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      exact n.2
    rw [momentShift_vv, momentShift_momentPair (-t) hdeg, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C, hσ, momentShift_algebraMap, map_neg, C_neg, sub_neg_eq_add, pow_comp,
      comp_X_sub_C_X_add_C, momentPair_X_pow]

/-! ## The equations in coordinates -/

variable (K r N) in
/-- The moment of index `m`, or `0` beyond the window. -/
noncomputable def vAt (m : ℕ) : IncRing K r N := if h : m < N then vv K r N ⟨m, h⟩ else 0

theorem momentPair_X_pow' (m : ℕ) : momentPair K r N (X ^ m) = vAt K r N m := by
  rw [vAt]
  split_ifs with h
  · exact momentPair_X_pow ⟨m, h⟩
  · refine Finset.sum_eq_zero fun n _ => ?_
    rw [coeff_X_pow, if_neg (fun (h' : (n : ℕ) = m) => h (h' ▸ n.2)), zero_mul]

/-- **The Hankel equations in coordinates**: `ℓ_j = ∑_i z_i v_{i+j}`. -/
theorem hankelEq_eq (j : ℕ) :
    hankelEq K r N j = ∑ i : Fin (r + 1), zv K r N i * vAt K r N (i + j) := by
  rw [hankelEq, gPoly, Finset.sum_mul, momentPair_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← pow_add, momentPair_C_mul, momentPair_X_pow']

/-! ## Regularity on the chart `z_0 ≠ 0` -/

section ChartZero

open MvPolynomial in
variable (K r N) in
/-- `K[z, v] ≅ K[z][v]`. -/
noncomputable def incEquiv :
    IncRing K r N ≃ₐ[K] MvPolynomial (Fin N) (MvPolynomial (Fin (r + 1)) K) :=
  (renameEquiv K (Equiv.sumComm _ _)).trans (sumAlgEquiv K (Fin N) (Fin (r + 1)))

theorem incEquiv_zv (i : Fin (r + 1)) :
    incEquiv K r N (zv K r N i) = MvPolynomial.C (MvPolynomial.X i) := by
  simp [incEquiv, zv]

theorem incEquiv_vv (n : Fin N) : incEquiv K r N (vv K r N n) = MvPolynomial.X n := by
  simp [incEquiv, vv]

theorem incEquiv_vAt (m : ℕ) :
    incEquiv K r N (vAt K r N m) = if h : m < N then MvPolynomial.X ⟨m, h⟩ else 0 := by
  rw [vAt]
  split_ifs
  · exact incEquiv_vv _
  · exact map_zero _

variable (K r) in
/-- The coefficient ring of the chart: `K[z]` with `z_0` inverted. -/
abbrev ChartBase := Localization.Away (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K)

attribute [local instance] MvPolynomial.algebraMvPolynomial

instance : IsDomain (ChartBase K r) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero _))

variable (K r) in
/-- The ratio `z_i / z_0`. -/
noncomputable def ratioCoeff (i : Fin (r + 1)) : ChartBase K r :=
  IsLocalization.mk' _ (MvPolynomial.X i) (⟨MvPolynomial.X 0, Submonoid.mem_powers _⟩ :
    Submonoid.powers (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K))

variable (K r N) in
/-- **The triangular tails** `φ_j = -∑_{i ≥ 1} (z_i / z_0) v_{i+j}`. -/
noncomputable def chartTail (j : Fin N) : MvPolynomial (Fin N) (ChartBase K r) :=
  if h : (j : ℕ) + r < N then
    -∑ i : Fin r, MvPolynomial.C (ratioCoeff K r i.succ) * MvPolynomial.X ⟨j + (i + 1), by omega⟩
  else 0

theorem chartTail_isTriangular : IsTriangular (chartTail K r N) := by
  classical
  intro j l hl
  rw [chartTail] at hl
  split_ifs at hl with h
  · rw [MvPolynomial.vars_neg] at hl
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hl)
    have h2 := MvPolynomial.vars_mul _ _ hi
    rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X] at h2
    rw [Finset.mem_singleton.mp h2, Fin.lt_def]
    simp only
    omega
  · simp at hl

variable (K r N) in
/-- The chart map `K[z, v] → K[z][z_0⁻¹][v]`. -/
noncomputable def chartMap : IncRing K r N →+* MvPolynomial (Fin N) (ChartBase K r) :=
  (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin (r + 1)) K))
    (MvPolynomial (Fin N) (ChartBase K r))).comp (incEquiv K r N).toRingHom

theorem chartMap_zv (i : Fin (r + 1)) :
    chartMap K r N (zv K r N i)
      = MvPolynomial.C (algebraMap (MvPolynomial (Fin (r + 1)) K) (ChartBase K r)
          (MvPolynomial.X i)) := by
  rw [chartMap, RingHom.comp_apply]
  change algebraMap _ _ (incEquiv K r N (zv K r N i)) = _
  rw [incEquiv_zv, MvPolynomial.algebraMap_def, MvPolynomial.map_C]

theorem chartMap_vv (n : Fin N) : chartMap K r N (vv K r N n) = MvPolynomial.X n := by
  rw [chartMap, RingHom.comp_apply]
  change algebraMap _ _ (incEquiv K r N (vv K r N n)) = _
  rw [incEquiv_vv, MvPolynomial.algebraMap_def, MvPolynomial.map_X]

theorem chartMap_vAt (m : ℕ) :
    chartMap K r N (vAt K r N m) = if h : m < N then MvPolynomial.X ⟨m, h⟩ else 0 := by
  rw [vAt]
  split_ifs
  · exact chartMap_vv _
  · exact map_zero _

variable (K r N) in
/-- The leading coefficient `z_0`, a unit on the chart. -/
noncomputable def chartUnit : MvPolynomial (Fin N) (ChartBase K r) :=
  MvPolynomial.C (algebraMap (MvPolynomial (Fin (r + 1)) K) (ChartBase K r) (MvPolynomial.X 0))

theorem isUnit_chartUnit : IsUnit (chartUnit K r N) :=
  (IsLocalization.Away.algebraMap_isUnit _).map MvPolynomial.C

theorem chartUnit_mul_ratioCoeff (i : Fin (r + 1)) :
    algebraMap (MvPolynomial (Fin (r + 1)) K) (ChartBase K r) (MvPolynomial.X 0) * ratioCoeff K r i
      = algebraMap (MvPolynomial (Fin (r + 1)) K) (ChartBase K r) (MvPolynomial.X i) := by
  rw [ratioCoeff, mul_comm]
  exact IsLocalization.mk'_spec _ _ _

/-- **On the chart, each Hankel equation is `z_0` times a triangular equation.** -/
theorem chartMap_hankelEq {j : ℕ} (hj : j + r < N) :
    chartMap K r N (hankelEq K r N j)
      = chartUnit K r N * triangularEq (chartTail K r N) ⟨j, by omega⟩ := by
  rw [hankelEq_eq, map_sum, Fin.sum_univ_succ, triangularEq, chartTail, dif_pos hj, sub_neg_eq_add,
    mul_add, Finset.mul_sum]
  congr 1
  · rw [map_mul, chartMap_zv, chartMap_vAt, dif_pos (by simp; omega)]
    simp [chartUnit]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, chartMap_zv, chartMap_vAt, dif_pos (by simp; omega), chartUnit, ← mul_assoc,
      ← map_mul, chartUnit_mul_ratioCoeff]
    congr 2
    simp only [Fin.val_succ]
    ext
    simp only
    omega

theorem chartMap_mem_triangularIdeal {j : ℕ} (hj : j + r ≤ N) {x : IncRing K r N}
    (hx : x ∈ hankelIdeal K r N j) : chartMap K r N x ∈ triangularIdeal (chartTail K r N) j := by
  have hle : hankelIdeal K r N j ≤ (triangularIdeal (chartTail K r N) j).comap (chartMap K r N) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m < j := hm
    change chartMap K r N (hankelEq K r N m) ∈ triangularIdeal (chartTail K r N) j
    rw [chartMap_hankelEq (by omega)]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨m, by omega⟩, hm', rfl⟩)
  exact hle hx

theorem triangularIdeal_le_map {j : ℕ} (hj : j + r ≤ N) :
    triangularIdeal (chartTail K r N) j ≤ (hankelIdeal K r N j).map (chartMap K r N) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  have hi' : (i : ℕ) < j := hi
  obtain ⟨u, hu⟩ := isUnit_chartUnit (K := K) (r := r) (N := N)
  have h1 : triangularEq (chartTail K r N) i
      = ↑u⁻¹ * chartMap K r N (hankelEq K r N i) := by
    rw [chartMap_hankelEq (by omega), ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  show triangularEq (chartTail K r N) i ∈ (hankelIdeal K r N j).map (chartMap K r N)
  rw [h1]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hankelEq_mem_hankelIdeal hi'))

/-- **Regularity on the chart `z_0 ≠ 0`**: the next Hankel equation is a nonzerodivisor modulo the
earlier ones after inverting `z_0`. -/
theorem chartReg_zero {j : ℕ} (hj : j + r < N) (x : IncRing K r N) (a : ℕ)
    (hx : zv K r N 0 ^ a * (hankelEq K r N j * x) ∈ hankelIdeal K r N j) :
    ∃ b : ℕ, zv K r N 0 ^ b * x ∈ hankelIdeal K r N j := by
  have h1 := chartMap_mem_triangularIdeal (le_of_lt hj) hx
  have hz : chartMap K r N (zv K r N 0) = chartUnit K r N := chartMap_zv 0
  rw [map_mul, map_mul, map_pow, chartMap_hankelEq hj, hz] at h1
  have h1' : (chartUnit K r N ^ a * chartUnit K r N)
      * (triangularEq (chartTail K r N) ⟨j, by omega⟩ * chartMap K r N x)
        ∈ triangularIdeal (chartTail K r N) j := by
    convert h1 using 1
    ring
  have hu : IsUnit (chartUnit K r N ^ a * chartUnit K r N) :=
    ((isUnit_chartUnit (K := K) (r := r) (N := N)).pow a).mul isUnit_chartUnit
  have h1 := (Ideal.unit_mul_mem_iff_mem _ hu).mp h1'
  have h3 : chartMap K r N x ∈ triangularIdeal (chartTail K r N) j := by
    have hnzd := triangular_mem_nonZeroDivisors (chartTail_isTriangular (K := K) (r := r) (N := N))
      (⟨j, by omega⟩ : Fin N)
    have hprod : Ideal.Quotient.mk (triangularIdeal (chartTail K r N) j)
          (triangularEq (chartTail K r N) ⟨j, by omega⟩)
        * Ideal.Quotient.mk (triangularIdeal (chartTail K r N) j) (chartMap K r N x) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd).mp hprod)
  have h4 := triangularIdeal_le_map (le_of_lt hj) h3
  rw [chartMap, ← Ideal.map_map] at h4
  haveI hloc : IsLocalization
      ((Submonoid.powers (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K)).map
        (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) (ChartBase K r)) :=
    MvPolynomial.isLocalization _ _
  obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((Submonoid.powers (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K)).map
      (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) (ChartBase K r)) _ _).mp h4
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨b, ?_⟩
  obtain ⟨y, hy, hyx⟩ :=
    (Ideal.mem_map_iff_of_surjective (incEquiv K r N).toRingHom (incEquiv K r N).surjective).mp hmem
  have hyx2 : incEquiv K r N y
      = MvPolynomial.C (MvPolynomial.X 0 ^ b) * incEquiv K r N x := hyx
  have hyx' : y = zv K r N 0 ^ b * x := by
    apply (incEquiv K r N).injective
    rw [hyx2]
    simp only [map_mul, map_pow, incEquiv_zv]
  rwa [← hyx']

end ChartZero

/-! ## Regularity on every evaluation chart -/

/-- **Chart regularity**: inverting `f`, the `j`-th Hankel equation is a nonzerodivisor modulo the
earlier ones. -/
def ChartReg (f : IncRing K r N) (j : ℕ) : Prop :=
  ∀ x : IncRing K r N, (∃ a : ℕ, f ^ a * (hankelEq K r N j * x) ∈ hankelIdeal K r N j) →
    ∃ b : ℕ, f ^ b * x ∈ hankelIdeal K r N j

theorem chartReg_zero' {j : ℕ} (hj : j + r < N) : ChartReg (zv K r N 0) j := by
  rintro x ⟨a, ha⟩
  exact chartReg_zero hj x a ha

/-- **Regularity on the chart `G(t) ≠ 0`**, transported by the moment shift. -/
theorem chartReg_chartForm (t : K) {j : ℕ} (hj : j + r < N) : ChartReg (chartForm K r N t) j := by
  rintro x ⟨a, ha⟩
  have hinv : ∀ y, momentShift K r N (-t) (momentShift K r N t y) = y := fun y =>
    DFunLike.congr_fun (momentShift_neg_comp t) y
  have hinv' : ∀ y, momentShift K r N t (momentShift K r N (-t) y) = y := fun y => by
    have := DFunLike.congr_fun (momentShift_neg_comp (K := K) (r := r) (N := N) (-t)) y
    rwa [neg_neg] at this
  have h1 := momentShift_mem_hankelIdeal (-t) (le_of_lt hj) ha
  rw [map_mul, map_pow, map_mul, ← momentShift_zv_zero t, hinv] at h1
  have hsub := momentShift_hankelEq_sub_mem (-t) hj
  have h2 : zv K r N 0 ^ a * (hankelEq K r N j * momentShift K r N (-t) x) ∈ hankelIdeal K r N j := by
    have : zv K r N 0 ^ a * (hankelEq K r N j * momentShift K r N (-t) x)
        = zv K r N 0 ^ a * (momentShift K r N (-t) (hankelEq K r N j) * momentShift K r N (-t) x)
          - zv K r N 0 ^ a * momentShift K r N (-t) x
            * (momentShift K r N (-t) (hankelEq K r N j) - hankelEq K r N j) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hsub)
  obtain ⟨b, hb⟩ := chartReg_zero hj _ a h2
  refine ⟨b, ?_⟩
  have h3 := momentShift_mem_hankelIdeal t (le_of_lt hj) hb
  rwa [map_mul, map_pow, momentShift_zv_zero, hinv'] at h3

/-- Chart regularity passes to smaller charts. -/
theorem ChartReg.mul {f : IncRing K r N} {j : ℕ} (hf : ChartReg f j) (c : IncRing K r N) :
    ChartReg (f * c) j := by
  rintro x ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hf (c ^ a * x) ⟨a, by
    have : f ^ a * (hankelEq K r N j * (c ^ a * x)) = (f * c) ^ a * (hankelEq K r N j * x) := by
      ring
    rw [this]
    exact ha⟩
  refine ⟨a + b, ?_⟩
  have : (f * c) ^ (a + b) * x = f ^ a * c ^ b * (f ^ b * (c ^ a * x)) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hb

end HTGeometry
