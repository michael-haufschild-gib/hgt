import GaloisForLFunctions.HTGeometry.HankelResolutionGlobalSections
import GaloisForLFunctions.HTGeometry.AwayLinearGenerators

/-!
# The charts of the Hankel incidence variety are affine spaces

On the chart `G(t) ≠ 0` of `Y = Proj B` (`B = K[z, v]/(ℓ_0, …, ℓ_{N-r-1})`), the degree-zero ring
`B_{(G(t))}` is a polynomial ring in `2r` variables.  After the moment shift `σ_t` (which carries
`z_0` to `G(t)`), the coordinates are `a_i = σ_t(z_{i+1}) / G(t)` (`i < r`) and the last `r`
moments `b_n = σ_t(v_{N-r+n})`: dehomogenizing `z_0 = 1`, the Hankel equations
`v_j = -∑_{i ≥ 1} z_i v_{i+j}` express the first `j` moments through the later ones (`B_j`).

* `HTGeometry.chartSol` : the solved moments, by downward recursion.
* `HTGeometry.incChartEval` : `K[z, v] → K[a, b]`, `z_0 ↦ 1`, killing the Hankel equations.
* `HTGeometry.chartRingEquiv` : `K[a, b] ≃+* B_{(G(t))}`.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

universe u

variable {K : Type u} [Field K] {r N : ℕ}

variable (K r) in
/-- The coordinate ring of a chart: `a_i` (`i < r`) and `b_n` (`n < f`). -/
abbrev ChartPoly (f : ℕ) := MvPolynomial (Fin r ⊕ Fin f) K

variable {j : ℕ}

variable (K r N) in
/-- **The solved moments**: `v_n = b_{n-j}` for `j ≤ n < N`, `v_n = 0` for `n ≥ N`, and
`v_n = -∑_{i<r} a_i v_{n+i+1}` for `n < j`. -/
noncomputable def chartSol (j n : ℕ) : ChartPoly K r (N - j) :=
  if h : j ≤ n then
    (if h' : n < N then MvPolynomial.X (Sum.inr ⟨n - j, by omega⟩) else 0)
  else -∑ i : Fin r, MvPolynomial.X (Sum.inl i) * chartSol j (n + i + 1)
termination_by j - n
decreasing_by omega

theorem chartSol_of_lt {n : ℕ} (h : n < j) :
    chartSol K r N j n = -∑ i : Fin r, MvPolynomial.X (Sum.inl i) * chartSol K r N j (n + i + 1) := by
  rw [chartSol, dif_neg (by omega)]

theorem chartSol_of_ge {n : ℕ} (h : N ≤ n) (hj : j ≤ N) : chartSol K r N j n = 0 := by
  rw [chartSol, dif_pos (by omega), dif_neg (by omega)]

theorem chartSol_tail (n : Fin (N - j)) (h : j ≤ N) :
    chartSol K r N j (j + n) = MvPolynomial.X (Sum.inr n) := by
  rw [chartSol, dif_pos (by omega), dif_pos (by omega)]
  congr 2
  ext
  simp only
  omega

variable (K r) in
/-- The images of the `z_i`: `z_0 ↦ 1`, `z_{i+1} ↦ a_i`. -/
noncomputable def chartZ (f : ℕ) : Fin (r + 1) → ChartPoly K r f :=
  Fin.cons 1 fun i => MvPolynomial.X (Sum.inl i)

variable (K r N) in
/-- **Dehomogenization and elimination**: `K[z, v] → K[a, b]`. -/
noncomputable def incChartEval (j : ℕ) : IncRing K r N →ₐ[K] ChartPoly K r (N - j) :=
  MvPolynomial.aeval (Sum.elim (chartZ K r (N - j)) fun n => chartSol K r N j n)

theorem incChartEval_zv (i : Fin (r + 1)) : incChartEval K r N j (zv K r N i) = chartZ K r (N - j) i := by
  simp [incChartEval, zv]

theorem incChartEval_vAt (hj : j ≤ N) (m : ℕ) :
    incChartEval K r N j (vAt K r N m) = chartSol K r N j m := by
  rw [vAt]
  split_ifs with h
  · simp [incChartEval, vv]
  · rw [map_zero, chartSol_of_ge (by omega) hj]

/-- **The dehomogenized Hankel equations hold.** -/
theorem incChartEval_hankelEq (hj : j + r ≤ N) {m : ℕ} (hm : m < j) :
    incChartEval K r N j (hankelEq K r N m) = 0 := by
  rw [hankelEq_eq, map_sum, Fin.sum_univ_succ]
  simp only [map_mul, incChartEval_zv, incChartEval_vAt (show j ≤ N by omega), chartZ,
    Fin.cons_zero, Fin.cons_succ, one_mul, Fin.val_zero, zero_add, Fin.val_succ]
  rw [chartSol_of_lt hm, neg_add_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ring

theorem incChartEval_mem_hankelIdeal (hj : j + r ≤ N) {x : IncRing K r N}
    (hx : x ∈ hankelIdeal K r N j) : incChartEval K r N j x = 0 := by
  have hle : hankelIdeal K r N j ≤ RingHom.ker (incChartEval K r N j).toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact incChartEval_hankelEq hj hm
  exact hle hx

/-! ## The moment shift is graded -/

open Polynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

theorem coeff_mem_of_forall {d : ℕ} {p : (IncRing K r N)[X]} (hp : ∀ i, p.coeff i ∈ 𝒵 d) (q : K[X])
    (i : ℕ) : (p * q.map (algebraMap K (IncRing K r N))).coeff i ∈ 𝒵 d := by
  rw [Polynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [Polynomial.coeff_map]
  simpa using SetLike.mul_mem_graded (hp x.1) (algebraMap_mem (r := r) (N := N) (q.coeff x.2))

theorem momentPair_mem {p : (IncRing K r N)[X]} (hp : ∀ i, p.coeff i ∈ 𝒵 0) :
    momentPair K r N p ∈ 𝒵 0 := by
  rw [momentPair]
  refine Submodule.sum_mem _ fun n _ => ?_
  simpa using SetLike.mul_mem_graded (hp n) (vv_mem (K := K) (r := r) n)

theorem X_sub_C_pow_eq_map (t : K) (n : ℕ) :
    (X - C (algebraMap K (IncRing K r N) t)) ^ n
      = ((X - C t) ^ n : K[X]).map (algebraMap K (IncRing K r N)) := by
  simp [Polynomial.map_pow, Polynomial.map_sub]

theorem X_add_C_pow_eq_map (t : K) (n : ℕ) :
    (X + C (algebraMap K (IncRing K r N) t)) ^ n
      = ((X + C t) ^ n : K[X]).map (algebraMap K (IncRing K r N)) := by
  simp [Polynomial.map_pow, Polynomial.map_add]

theorem momentShift_zv_mem (t : K) (i : Fin (r + 1)) : momentShift K r N t (zv K r N i) ∈ 𝒵 1 := by
  rw [momentShift_zv, gPoly, Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, X_add_C_pow_eq_map,
    Polynomial.coeff_C_mul, Polynomial.coeff_map]
  simpa using SetLike.mul_mem_graded (zv_mem (K := K) (N := N) l)
    (algebraMap_mem (r := r) (N := N) (((X + C t) ^ (l : ℕ) : K[X]).coeff i))

theorem momentShift_vv_mem (t : K) (n : Fin N) : momentShift K r N t (vv K r N n) ∈ 𝒵 0 := by
  rw [momentShift_vv]
  refine momentPair_mem fun i => ?_
  rw [X_sub_C_pow_eq_map, Polynomial.coeff_map]
  exact algebraMap_mem _

/-- **The moment shift preserves the grading.** -/
theorem momentShift_mem {t : K} {d : ℕ} {x : IncRing K r N} (hx : x ∈ 𝒵 d) :
    momentShift K r N t x ∈ 𝒵 d := by
  refine aeval_mem_projGrading ?_ hx
  rintro (i | n)
  · have h := momentShift_zv_mem (N := N) t i
    rw [momentShift_zv] at h
    simpa [projWeight] using h
  · have h := momentShift_vv_mem (r := r) t n
    rw [momentShift_vv] at h
    simpa [projWeight] using h

theorem momentShift_inv (t : K) (y : IncRing K r N) :
    momentShift K r N (-t) (momentShift K r N t y) = y :=
  DFunLike.congr_fun (momentShift_neg_comp t) y

theorem momentShift_inv' (t : K) (y : IncRing K r N) :
    momentShift K r N t (momentShift K r N (-t) y) = y := by
  have := DFunLike.congr_fun (momentShift_neg_comp (K := K) (r := r) (N := N) (-t)) y
  rwa [neg_neg] at this

/-! ## The chart `G(t) ≠ 0` -/

section Chart

open HomogeneousLocalization

local notation "𝒜" => quotGrading K r N j

variable (K r N j) in
/-- The chart form `G(t)` in `B`. -/
noncomputable abbrev tChart (t : K) : HankelQuot K r N j :=
  Ideal.Quotient.mk _ (chartForm K r N t)

theorem tChart_mem (t : K) : tChart K r N j t ∈ 𝒜 1 := mk_mem_piece 𝒵 _ (chartForm_mem t)

variable (K r N j) in
/-- The shifted projective coordinates `σ_t(z_i)` in `B`. -/
noncomputable def shiftZ (t : K) (i : Fin (r + 1)) : HankelQuot K r N j :=
  Ideal.Quotient.mk _ (momentShift K r N t (zv K r N i))

theorem shiftZ_mem (t : K) (i : Fin (r + 1)) : shiftZ K r N j t i ∈ 𝒜 1 :=
  mk_mem_piece 𝒵 _ (momentShift_mem (zv_mem i))

theorem shiftZ_zero (t : K) : shiftZ K r N j t 0 = tChart K r N j t := by
  rw [shiftZ, momentShift_zv_zero]

variable (K r N j) in
/-- The shifted moments `σ_t(v_m)` in degree zero of `B`. -/
noncomputable def shiftV (t : K) (m : ℕ) : 𝒜 0 :=
  ⟨Ideal.Quotient.mk _ (momentShift K r N t (vAt K r N m)),
    mk_mem_piece 𝒵 _ (momentShift_mem (vAt_mem m))⟩

variable (K r N) in
/-- **The chart evaluation of `B`**: `x ↦ incChartEval (σ_{-t} x)`. -/
noncomputable def chartQuotEval (hj : j + r ≤ N) (t : K) :
    HankelQuot K r N j →ₐ[K] ChartPoly K r (N - j) :=
  Ideal.Quotient.liftₐ _ ((incChartEval K r N j).comp (momentShift K r N (-t))) fun x hx =>
    incChartEval_mem_hankelIdeal hj (momentShift_mem_hankelIdeal (-t) hj hx)

theorem chartQuotEval_mk (hj : j + r ≤ N) (t : K) (x : IncRing K r N) :
    chartQuotEval K r N hj t (Ideal.Quotient.mk _ x)
      = incChartEval K r N j (momentShift K r N (-t) x) := rfl

theorem chartQuotEval_shiftZ (hj : j + r ≤ N) (t : K) (i : Fin (r + 1)) :
    chartQuotEval K r N hj t (shiftZ K r N j t i) = chartZ K r (N - j) i := by
  rw [shiftZ, chartQuotEval_mk, momentShift_inv, incChartEval_zv]

theorem chartQuotEval_shiftV (hj : j + r ≤ N) (t : K) (m : ℕ) :
    chartQuotEval K r N hj t (shiftV K r N j t m : HankelQuot K r N j) = chartSol K r N j m := by
  rw [shiftV, chartQuotEval_mk, momentShift_inv, incChartEval_vAt (by omega)]

theorem chartQuotEval_tChart (hj : j + r ≤ N) (t : K) : chartQuotEval K r N hj t (tChart K r N j t) = 1 := by
  rw [← shiftZ_zero, chartQuotEval_shiftZ]
  rfl

variable (K r N) in
/-- **The chart ring to the polynomial ring.** -/
noncomputable def chartPsi (hj : j + r ≤ N) (t : K) : Away 𝒜 (tChart K r N j t) →+* ChartPoly K r (N - j) :=
  (IsLocalization.Away.lift (tChart K r N j t) (g := (chartQuotEval K r N hj t).toRingHom)
    (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartQuotEval_tChart]; exact isUnit_one)).comp
    (algebraMap (Away 𝒜 (tChart K r N j t)) (Localization.Away (tChart K r N j t)))

theorem chartPsi_fromZero (hj : j + r ≤ N) (t : K) (x : 𝒜 0) :
    chartPsi K r N hj t (fromZeroRingHom 𝒜 _ x) = chartQuotEval K r N hj t x := by
  rw [chartPsi, RingHom.comp_apply]
  change IsLocalization.Away.lift _ _ (fromZeroRingHom 𝒜 _ x).val = _
  rw [val_fromZeroRingHom, IsLocalization.Away.lift_eq]
  rfl

theorem chartPsi_linFrac (hj : j + r ≤ N) (t : K) {u : HankelQuot K r N j} (hu : u ∈ 𝒜 1) :
    chartPsi K r N hj t (linFrac (tChart_mem t) hu) = chartQuotEval K r N hj t u := by
  rw [chartPsi, RingHom.comp_apply]
  change IsLocalization.Away.lift _ _ (linFrac (tChart_mem t) hu).val = _
  set L := IsLocalization.Away.lift (tChart K r N j t) (S := Localization.Away (tChart K r N j t))
    (g := (chartQuotEval K r N hj t).toRingHom)
    (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartQuotEval_tChart]; exact isUnit_one)
  have h1 : (linFrac (tChart_mem t) hu).val * algebraMap _ (Localization.Away (tChart K r N j t))
      (tChart K r N j t) = algebraMap _ _ u := by
    rw [val_linFrac, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg L h1
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at h2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartQuotEval_tChart, mul_one] at h2
  exact h2

variable (K r N j) in
/-- **The polynomial ring to the chart ring**: `a_i ↦ σ_t(z_{i+1}) / G(t)`,
`b_n ↦ σ_t(v_{N-r+n})`. -/
noncomputable def chartPhi (t : K) : ChartPoly K r (N - j) →+* Away 𝒜 (tChart K r N j t) :=
  MvPolynomial.eval₂Hom ((fromZeroRingHom 𝒜 _).comp (algebraMap K (𝒜 0)))
    (Sum.elim (fun i => linFrac (tChart_mem t) (shiftZ_mem t i.succ))
      (fun n => fromZeroRingHom 𝒜 _ (shiftV K r N j t (j + n))))

/-- **`Ψ ∘ Φ = id`.** -/
theorem chartPsi_chartPhi (hj : j + r ≤ N) (t : K) (p : ChartPoly K r (N - j)) :
    chartPsi K r N hj t (chartPhi K r N j t p) = p := by
  have h : (chartPsi K r N hj t).comp (chartPhi K r N j t) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · rw [RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        chartPsi_fromZero]
      exact AlgHom.commutes _ c
    · rcases k with i | n
      · rw [RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inl, chartPsi_linFrac,
          chartQuotEval_shiftZ]
        rfl
      · rw [RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inr, chartPsi_fromZero,
          chartQuotEval_shiftV, chartSol_tail n (by omega)]
        rfl
  exact DFunLike.congr_fun h p

/-! ### Surjectivity of `Φ` -/

/-- The shifted Hankel relations in `B`: `∑_i σ_t(z_i) σ_t(v_{i+m}) = 0`. -/
theorem sum_shiftZ_mul_shiftV (hj : j + r ≤ N) (t : K) {m : ℕ} (hm : m < j) :
    ∑ i : Fin (r + 1), shiftZ K r N j t i * (shiftV K r N j t (i + m) : HankelQuot K r N j) = 0 := by
  have h0 : (Ideal.Quotient.mk _ (momentShift K r N t (hankelEq K r N m)) :
      HankelQuot K r N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (momentShift_hankelEq_mem t hm (by omega))
  rw [← h0, hankelEq_eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul]
  rfl

/-- **The shifted relations in the chart**: `σ_t(v_m) = -∑_{i<r} a_i σ_t(v_{m+i+1})`. -/
theorem fromZero_shiftV_eq (hj : j + r ≤ N) (t : K) {m : ℕ} (hm : m < j) :
    fromZeroRingHom 𝒜 _ (shiftV K r N j t m) = -∑ i : Fin r,
      linFrac (tChart_mem t) (shiftZ_mem t i.succ) *
        fromZeroRingHom 𝒜 _ (shiftV K r N j t (i + 1 + m)) := by
  have hmem : ∀ i : Fin (r + 1), shiftZ K r N j t i * (shiftV K r N j t (i + m) : HankelQuot K r N j)
      ∈ 𝒜 1 := fun i => by
    simpa using SetLike.mul_mem_graded (shiftZ_mem t i) (shiftV K r N j t (i + m)).2
  have h1 := linFrac_sum (tChart_mem t) Finset.univ _ hmem
  rw [linFrac_congr _ _ (sum_shiftZ_mul_shiftV hj t hm)] at h1
  have h2 : linFrac (tChart_mem (K := K) (r := r) (N := N) t) (zero_mem (𝒜 1)) = 0 := linFrac_zero _
  rw [h2, Fin.sum_univ_succ] at h1
  rw [eq_neg_iff_add_eq_zero]
  refine Eq.trans ?_ h1.symm
  congr 1
  · rw [linFrac_mul_zero (tChart_mem t) (shiftZ_mem t 0)
      (shiftV K r N j t (((0 : Fin (r + 1)) : ℕ) + m)).2,
      linFrac_of_eq _ _ (shiftZ_zero t), one_mul, Fin.val_zero, zero_add]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [linFrac_mul_zero (tChart_mem t) (shiftZ_mem t i.succ)
      (shiftV K r N j t (((i.succ : Fin (r + 1)) : ℕ) + m)).2,
      Fin.val_succ]

theorem fromZero_shiftV_mem_range (hj : j + r ≤ N) (t : K) (m : ℕ) :
    fromZeroRingHom 𝒜 _ (shiftV K r N j t m) ∈ (chartPhi K r N j t).range := by
  induction hk : N - m using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    by_cases h1 : N ≤ m
    · have h0 : shiftV K r N j t m = 0 := by
        apply Subtype.ext
        simp [shiftV, vAt, dif_neg (show ¬ m < N by omega)]
      rw [h0, map_zero]
      exact Subring.zero_mem _
    by_cases h2 : j ≤ m
    · refine ⟨MvPolynomial.X (Sum.inr ⟨m - j, by omega⟩), ?_⟩
      rw [chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inr]
      congr 2
      simp only
      omega
    · rw [fromZero_shiftV_eq hj t (by omega)]
      refine Subring.neg_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ ⟨MvPolynomial.X
        (Sum.inl i), ?_⟩ (ih (N - (i + 1 + m)) (by omega) _ rfl))
      rw [chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inl]

variable (K r N j) in
/-- The shifted moments as a ring map `K[x] → B_0`. -/
noncomputable def shiftToZero (t : K) : MvPolynomial (Fin N) K →+* 𝒜 0 where
  toFun P := ⟨Ideal.Quotient.mk _ (momentShift K r N t (momentEmbed K r N P)),
    mk_mem_piece 𝒵 _ (momentShift_mem (momentEmbed_mem P))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' P Q := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by simp)

theorem fromZero_shiftToZero_mem_range (hj : j + r ≤ N) (t : K) (P : MvPolynomial (Fin N) K) :
    fromZeroRingHom 𝒜 _ (shiftToZero K r N j t P) ∈ (chartPhi K r N j t).range := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, ?_⟩
    rw [chartPhi, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    congr 1
    apply Subtype.ext
    simp [shiftToZero, momentEmbed]
    rfl
  | add p q hp hq =>
    rw [RingHom.map_add, RingHom.map_add]
    exact Subring.add_mem _ hp hq
  | mul_X p n hp =>
    rw [RingHom.map_mul, RingHom.map_mul]
    refine Subring.mul_mem _ hp ?_
    have hn : shiftToZero K r N j t (MvPolynomial.X n) = shiftV K r N j t n := by
      apply Subtype.ext
      simp only [shiftToZero, shiftV, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, momentEmbed_X,
        vAt, dif_pos n.2]
    rw [hn]
    exact fromZero_shiftV_mem_range hj t n

theorem fromZero_mem_range (hj : j + r ≤ N) (t : K) (x : 𝒜 0) :
    fromZeroRingHom 𝒜 _ x ∈ (chartPhi K r N j t).range := by
  obtain ⟨y, hy, hyx⟩ := x.2
  obtain ⟨P, hP⟩ := exists_momentEmbed_eq (momentShift_mem (t := -t) hy)
  have hx : x = shiftToZero K r N j t P := by
    apply Subtype.ext
    change _ = Ideal.Quotient.mk _ (momentShift K r N t (momentEmbed K r N P))
    rw [hP, momentShift_inv']
    exact hyx.symm
  rw [hx]
  exact fromZero_shiftToZero_mem_range hj t P

/-- **The shifted projective coordinates generate `B` over `B_0`.** -/
theorem adjoin_shiftZ_eq_top (t : K) :
    Algebra.adjoin (𝒜 0) (Set.range (shiftZ K r N j t)) = ⊤ := by
  rw [eq_top_iff]
  rintro b -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← momentShift_inv' t p]
  induction momentShift K r N (-t) p using MvPolynomial.induction_on with
  | C c =>
    have : (Ideal.Quotient.mk _ (momentShift K r N t (MvPolynomial.C c)) : HankelQuot K r N j)
        = algebraMap (𝒜 0) _ (algebraMap K (𝒜 0) c) := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add, map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p k hp =>
    rw [map_mul, map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    rcases k with i | n
    · exact Algebra.subset_adjoin ⟨i, rfl⟩
    · have : (Ideal.Quotient.mk _ (momentShift K r N t (MvPolynomial.X (Sum.inr n))) :
          HankelQuot K r N j) = algebraMap (𝒜 0) _ (shiftV K r N j t n) := by
        change _ = Ideal.Quotient.mk _ (momentShift K r N t (vAt K r N n))
        rw [vAt, dif_pos n.2]
        rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _

/-- **`Φ` is surjective.** -/
theorem chartPhi_surjective (hj : j + r ≤ N) (t : K) : Function.Surjective (chartPhi K r N j t) := by
  let S : Subalgebra (𝒜 0) (Away 𝒜 (tChart K r N j t)) :=
    { (chartPhi K r N j t).rangeS with algebraMap_mem' := fun x => fromZero_mem_range hj t x }
  have hS : Algebra.adjoin (𝒜 0) (Set.range fun i => linFrac (tChart_mem t) (shiftZ_mem t i)) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · dsimp only
      rw [linFrac_of_eq _ _ (shiftZ_zero t)]
      exact S.one_mem
    · exact ⟨MvPolynomial.X (Sum.inl j), by rw [chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inl]⟩
  rw [away_adjoin_linear_eq_top (tChart_mem t) (shiftZ K r N j t) (shiftZ_mem t)
    (adjoin_shiftZ_eq_top t)] at hS
  intro y
  exact hS (Algebra.mem_top (x := y))

variable (K r N) in
/-- **The chart ring is a polynomial ring in `2r` variables.** -/
noncomputable def chartRingEquiv (hj : j + r ≤ N) (t : K) : ChartPoly K r (N - j) ≃+* Away 𝒜 (tChart K r N j t) :=
  RingEquiv.ofBijective (chartPhi K r N j t)
    ⟨Function.LeftInverse.injective (chartPsi_chartPhi hj t), chartPhi_surjective hj t⟩

theorem chartRingEquiv_C (hj : j + r ≤ N) (t : K) (c : K) :
    chartRingEquiv K r N hj t (MvPolynomial.C c)
      = fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c) := by
  change chartPhi K r N j t _ = _
  rw [chartPhi, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

instance (t : K) [Fact (j + r ≤ N)] : IsDomain (Away 𝒜 (tChart K r N j t)) :=
  (chartRingEquiv K r N Fact.out t).symm.toMulEquiv.isDomain _

end Chart

end HTGeometry
