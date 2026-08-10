import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderExteriorSquare

/-!
# The trace-dual lattice of the diagonal congruence order

For the diagonal congruence order `A = R·1 + a·O` inside `O = R^N` the coordinate trace pairing
`⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` on the total quotient algebra `K^N` has dual lattice

`A♯ = a⁻¹ · {z ∈ R^N : a ∣ ∑ᵢ zᵢ}`,

and the resulting trace-law defect `A♯ / A` is `(R/a²)^{N−1}`.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## Lattices inside the total quotient algebra -/

section Lattices

variable {R : Type*} [CommRing R]

/-- The coordinate sum functional. -/
def congruenceSumForm (R : Type*) [CommRing R] (N : ℕ) : (Fin N → R) →ₗ[R] R :=
  ∑ i, LinearMap.proj i

theorem congruenceSumForm_apply {N : ℕ} (z : Fin N → R) : congruenceSumForm R N z = ∑ i, z i := by
  simp [congruenceSumForm, LinearMap.sum_apply]

/-- The rescaled dual lattice `a·A♯ = {z ∈ R^N : a ∣ ∑ᵢ zᵢ}`. -/
def scaledDual (a : R) (N : ℕ) : Submodule R (Fin N → R) :=
  Submodule.comap (congruenceSumForm R N) (Ideal.span ({a} : Set R))

theorem mem_scaledDual {a : R} {N : ℕ} {z : Fin N → R} :
    z ∈ scaledDual a N ↔ a ∣ ∑ i, z i := by
  rw [scaledDual, Submodule.mem_comap, congruenceSumForm_apply, Ideal.mem_span_singleton]

/-- The rescaled order `a·A`. -/
def scaledOrder (a : R) (N : ℕ) : Submodule R (Fin N → R) :=
  Submodule.map (a • LinearMap.id) (Subalgebra.toSubmodule (congruenceOrder a N))

theorem mem_scaledOrder {a : R} {N : ℕ} {z : Fin N → R} :
    z ∈ scaledOrder a N ↔ ∃ v ∈ congruenceOrder a N, a • v = z := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem aSingle_mem_congruenceOrder (a : R) {N : ℕ} (j : Fin N) :
    (a • Pi.single j 1 : Fin N → R) ∈ congruenceOrder a N := by
  classical
  intro l l'
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  exact ⟨(if l = j then 1 else 0) - (if l' = j then 1 else 0), by ring⟩

theorem scaledOrder_le_scaledDual (a : R) (N : ℕ) :
    scaledOrder a N ≤ scaledDual a N := by
  rintro z ⟨v, _, rfl⟩
  refine mem_scaledDual.2 ⟨∑ i, v i, ?_⟩
  show ∑ i, (a • v) i = a * ∑ i, v i
  rw [Finset.mul_sum]
  rfl

end Lattices

/-! ## The trace-dual lattice -/

section TraceDual

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The trace-dual lattice `A♯ = {y ∈ K^N : ⟨x, y⟩ ∈ R for every x ∈ A}`. -/
def traceDual (a : R) (N : ℕ) : Submodule R (Fin N → K) where
  carrier := {y | ∀ x ∈ congruenceOrder a N,
    ∃ r : R, ∑ i, algebraMap R K (x i) * y i = algebraMap R K r}
  add_mem' := by
    rintro y y' hy hy' x hx
    obtain ⟨r, hr⟩ := hy x hx
    obtain ⟨r', hr'⟩ := hy' x hx
    refine ⟨r + r', ?_⟩
    have hsplit : ∀ i, algebraMap R K (x i) * (y + y') i
        = algebraMap R K (x i) * y i + algebraMap R K (x i) * y' i := by
      intro i
      show algebraMap R K (x i) * (y i + y' i) = _
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, hr, hr', map_add]
  zero_mem' := by
    intro x _
    exact ⟨0, by simp⟩
  smul_mem' := by
    rintro c y hy x hx
    obtain ⟨r, hr⟩ := hy x hx
    refine ⟨c * r, ?_⟩
    have hsplit : ∀ i, algebraMap R K (x i) * (c • y) i
        = algebraMap R K c * (algebraMap R K (x i) * y i) := by
      intro i
      show algebraMap R K (x i) * (c • y i) = _
      rw [Algebra.smul_def]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum, hr, ← map_mul]

omit [IsFractionRing R K] in
theorem mem_traceDual {a : R} {N : ℕ} {y : Fin N → K} :
    y ∈ traceDual (K := K) a N ↔ ∀ x ∈ congruenceOrder a N,
      ∃ r : R, ∑ i, algebraMap R K (x i) * y i = algebraMap R K r := Iff.rfl

theorem algebraMap_ne_zero_of_ne_zero {a : R} (ha : a ≠ 0) : algebraMap R K a ≠ 0 :=
  fun h => ha (IsFractionRing.injective R K (by rw [h, map_zero]))

omit [IsFractionRing R K] in
theorem sum_aSingle_pairing {a : R} {N : ℕ} (y : Fin N → K) (j : Fin N) :
    ∑ i, algebraMap R K ((a • Pi.single j (1 : R) : Fin N → R) i) * y i
      = algebraMap R K a * y j := by
  classical
  rw [Finset.sum_eq_single j]
  · show algebraMap R K (a * (Pi.single j (1 : R) : Fin N → R) j) * y j = _
    rw [Pi.single_eq_same, mul_one]
  · intro i _ hi
    show algebraMap R K (a * (Pi.single j (1 : R) : Fin N → R) i) * y i = 0
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [IsFractionRing R K] in
theorem sum_one_pairing {N : ℕ} (y : Fin N → K) :
    ∑ i, algebraMap R K ((1 : Fin N → R) i) * y i = ∑ i, y i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  show algebraMap R K (1 : R) * y i = y i
  rw [map_one, one_mul]

/-- **Card `(9)`.**  The trace dual of the diagonal congruence order consists of the vectors whose
`a`-multiple is integral with coordinate sum divisible by `a`. -/
theorem mem_traceDual_iff {a : R} (ha : a ≠ 0) {m : ℕ} {y : Fin (m + 1) → K} :
    y ∈ traceDual (K := K) a (m + 1) ↔
      ∃ z : Fin (m + 1) → R, (a ∣ ∑ i, z i) ∧
        ∀ i, algebraMap R K a * y i = algebraMap R K (z i) := by
  constructor
  · intro hy
    choose z hz using fun j => hy _ (aSingle_mem_congruenceOrder a j)
    have hzy : ∀ j, algebraMap R K a * y j = algebraMap R K (z j) := by
      intro j
      rw [← sum_aSingle_pairing y j]
      exact hz j
    obtain ⟨s, hs⟩ := hy 1 (congruenceOrder a (m + 1)).one_mem
    rw [sum_one_pairing] at hs
    refine ⟨z, ⟨s, ?_⟩, hzy⟩
    refine IsFractionRing.injective R K ?_
    rw [map_sum, map_mul, ← hs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (hzy i).symm
  · rintro ⟨z, ⟨s, hs⟩, hzy⟩
    have hsum : ∑ i, y i = algebraMap R K s := by
      have h1 : algebraMap R K a * ∑ i, y i = algebraMap R K a * algebraMap R K s := by
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hzy i), ← map_sum, hs, map_mul]
      exact mul_left_cancel₀ (algebraMap_ne_zero_of_ne_zero ha) h1
    intro x hx
    choose c hc using fun i => hx i (Fin.last m)
    refine ⟨x (Fin.last m) * s + ∑ i, c i * z i, ?_⟩
    have hx' : ∀ i, x i = x (Fin.last m) + a * c i := by
      intro i
      have := hc i
      linear_combination this
    have hterm : ∀ i, algebraMap R K (x i) * y i
        = algebraMap R K (x (Fin.last m)) * y i
          + algebraMap R K (c i) * (algebraMap R K a * y i) := by
      intro i
      rw [hx', map_add, map_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum, Finset.sum_congr rfl (fun i _ => by rw [hzy i] : ∀ i ∈ Finset.univ,
        algebraMap R K (c i) * (algebraMap R K a * y i)
          = algebraMap R K (c i) * algebraMap R K (z i)),
      map_add, map_mul, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm)

/-- The rescaling `z ↦ z / a` from the integral lattice into the total quotient algebra. -/
noncomputable def dualScaleMap (a : R) (N : ℕ) : (Fin N → R) →ₗ[R] (Fin N → K) where
  toFun z i := algebraMap R K (z i) / algebraMap R K a
  map_add' z w := by
    funext i
    show algebraMap R K (z i + w i) / algebraMap R K a = _
    rw [map_add]
    show _ = algebraMap R K (z i) / algebraMap R K a + algebraMap R K (w i) / algebraMap R K a
    ring
  map_smul' r z := by
    funext i
    show algebraMap R K (r * z i) / algebraMap R K a
      = (r • fun i => algebraMap R K (z i) / algebraMap R K a) i
    rw [map_mul]
    show _ = r • (algebraMap R K (z i) / algebraMap R K a)
    rw [Algebra.smul_def]
    ring

omit [IsFractionRing R K] in
theorem dualScaleMap_apply {a : R} {N : ℕ} (z : Fin N → R) (i : Fin N) :
    dualScaleMap (K := K) a N z i = algebraMap R K (z i) / algebraMap R K a := rfl

theorem dualScaleMap_injective {a : R} (ha : a ≠ 0) (N : ℕ) :
    Function.Injective (dualScaleMap (K := K) a N) := by
  intro z w h
  funext i
  have hi := congrFun h i
  rw [dualScaleMap_apply, dualScaleMap_apply,
    div_eq_div_iff (algebraMap_ne_zero_of_ne_zero ha) (algebraMap_ne_zero_of_ne_zero ha)] at hi
  exact IsFractionRing.injective R K (mul_right_cancel₀ (algebraMap_ne_zero_of_ne_zero ha) hi)

theorem dualScaleMap_eq_iff {a : R} (ha : a ≠ 0) {N : ℕ} (z : Fin N → R) (y : Fin N → K) :
    dualScaleMap (K := K) a N z = y ↔ ∀ i, algebraMap R K a * y i = algebraMap R K (z i) := by
  constructor
  · rintro rfl i
    rw [dualScaleMap_apply, mul_div_cancel₀ _ (algebraMap_ne_zero_of_ne_zero ha)]
  · intro h
    funext i
    rw [dualScaleMap_apply, div_eq_iff (algebraMap_ne_zero_of_ne_zero ha), ← h i]
    ring

/-- **Card `(9)`, lattice form.**  `A♯ = a⁻¹ · {z : a ∣ ∑ zᵢ}`. -/
theorem traceDual_eq_map {a : R} (ha : a ≠ 0) (m : ℕ) :
    traceDual (K := K) a (m + 1)
      = Submodule.map (dualScaleMap (K := K) a (m + 1)) (scaledDual a (m + 1)) := by
  ext y
  rw [mem_traceDual_iff ha, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, mem_scaledDual.2 hz, (dualScaleMap_eq_iff ha z y).2 hzy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, mem_scaledDual.1 hz, (dualScaleMap_eq_iff ha z y).1 hzy⟩

/-- The coordinatewise inclusion of the integral lattice into the total quotient algebra. -/
def coordIncl (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] (N : ℕ) :
    (Fin N → R) →ₗ[R] (Fin N → K) :=
  LinearMap.pi fun i => (Algebra.linearMap R K).comp (LinearMap.proj i)

omit [IsFractionRing R K] in
theorem coordIncl_apply {N : ℕ} (z : Fin N → R) (i : Fin N) :
    coordIncl R K N z i = algebraMap R K (z i) := rfl

/-- The order itself, embedded in the total quotient algebra. -/
def orderLattice (a : R) (N : ℕ) : Submodule R (Fin N → K) :=
  Submodule.map (coordIncl R K N) (Subalgebra.toSubmodule (congruenceOrder a N))

theorem dualScaleMap_aSmul_eq {a : R} (ha : a ≠ 0) {N : ℕ} (v : Fin N → R) :
    dualScaleMap (K := K) a N (a • v) = coordIncl R K N v := by
  funext i
  rw [dualScaleMap_apply]
  show algebraMap R K (a * v i) / algebraMap R K a = algebraMap R K (v i)
  rw [map_mul, mul_comm, mul_div_assoc, div_self (algebraMap_ne_zero_of_ne_zero ha), mul_one]

theorem orderLattice_eq_map {a : R} (ha : a ≠ 0) (N : ℕ) :
    orderLattice (K := K) a N
      = Submodule.map (dualScaleMap (K := K) a N) (scaledOrder a N) := by
  ext y
  rw [orderLattice, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨a • v, ⟨v, hv, rfl⟩, dualScaleMap_aSmul_eq ha v⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨v, hv, (dualScaleMap_aSmul_eq ha v).symm⟩

end TraceDual

/-! ## The trace-law defect -/

section TraceDefect

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [Invertible ((m : R) + 1)]

/-- The centred coordinates `zᵢ − N⁻¹·∑ⱼ zⱼ` of a vector, for the first `N−1` sheets. -/
noncomputable def traceCoordRaw (m : ℕ) [Invertible ((m : R) + 1)] :
    (Fin (m + 1) → R) →ₗ[R] (Fin m → R) :=
  LinearMap.pi fun i =>
    (LinearMap.proj i.castSucc : (Fin (m + 1) → R) →ₗ[R] R)
      - (⅟((m : R) + 1)) • congruenceSumForm R (m + 1)

theorem traceCoordRaw_apply (z : Fin (m + 1) → R) (i : Fin m) :
    traceCoordRaw (R := R) m z i = z i.castSucc - ⅟((m : R) + 1) * ∑ j, z j := by
  show z i.castSucc - ⅟((m : R) + 1) • congruenceSumForm R (m + 1) z = _
  rw [congruenceSumForm_apply, smul_eq_mul]

/-- The trace-law defect coordinates, taken modulo `a²`. -/
noncomputable def traceCoord (a : R) (m : ℕ) [Invertible ((m : R) + 1)] :
    (Fin (m + 1) → R) →ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  LinearMap.pi fun i =>
    (Ideal.span ({a ^ 2} : Set R)).mkQ.comp ((LinearMap.proj i).comp (traceCoordRaw m))

theorem traceCoord_apply (z : Fin (m + 1) → R) (i : Fin m) :
    traceCoord a m z i
      = Submodule.Quotient.mk (z i.castSucc - ⅟((m : R) + 1) * ∑ j, z j) := by
  show Submodule.Quotient.mk (traceCoordRaw m z i) = _
  rw [traceCoordRaw_apply]

theorem traceCoord_eq_zero_iff (z : Fin (m + 1) → R) :
    traceCoord a m z = 0 ↔
      ∀ i : Fin m, a ^ 2 ∣ z i.castSucc - ⅟((m : R) + 1) * ∑ j, z j := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [traceCoord_apply] at hi
    exact Ideal.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 hi)
  · intro h
    funext i
    rw [traceCoord_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (h i))

theorem traceCoord_scaledOrder {z : Fin (m + 1) → R} (hz : z ∈ scaledOrder a (m + 1)) :
    traceCoord a m z = 0 := by
  obtain ⟨v, hv, rfl⟩ := mem_scaledOrder.1 hz
  rw [traceCoord_eq_zero_iff]
  intro i
  choose d hd using fun j => hv i.castSucc j
  refine ⟨⅟((m : R) + 1) * ∑ j, d j, ?_⟩
  have hsum : ∑ j, (a • v) j = a * ∑ j, v j := by
    rw [Finset.mul_sum]
    rfl
  have hconst : ((m : R) + 1) * v i.castSucc = ∑ _j : Fin (m + 1), v i.castSucc := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
  have hA : ((m : R) + 1) * v i.castSucc - ∑ j, v j = a * ∑ j, d j := by
    rw [hconst, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hd j
  have hB : ⅟((m : R) + 1) * ((m : R) + 1) = 1 := invOf_mul_self _
  show a * v i.castSucc - ⅟((m : R) + 1) * ∑ j, (a • v) j = _
  rw [hsum]
  linear_combination (a * ⅟((m : R) + 1)) * hA - (a * v i.castSucc) * hB

theorem traceCoord_surjective_scaledDual (w : Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :
    ∃ z ∈ scaledDual a (m + 1), traceCoord a m z = w := by
  classical
  choose c hc using fun i =>
    Submodule.Quotient.mk_surjective (Ideal.span ({a ^ 2} : Set R)) (w i)
  have hzero : ∑ j, (Fin.snoc c (-(∑ i, c i)) : Fin (m + 1) → R) j = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp
  refine ⟨Fin.snoc c (-(∑ i, c i)), mem_scaledDual.2 ⟨0, by rw [hzero, mul_zero]⟩, ?_⟩
  funext i
  rw [traceCoord_apply, hzero, mul_zero, sub_zero, Fin.snoc_castSucc]
  exact hc i

theorem mem_scaledOrder_of_traceCoord {z : Fin (m + 1) → R}
    (hz : z ∈ scaledDual a (m + 1)) (h0 : traceCoord a m z = 0) :
    z ∈ scaledOrder a (m + 1) := by
  classical
  obtain ⟨t, ht⟩ := mem_scaledDual.1 hz
  rw [traceCoord_eq_zero_iff] at h0
  choose u' hu' using h0
  have hB : ⅟((m : R) + 1) * ((m : R) + 1) = 1 := invOf_mul_self _
  have hS : ∑ i : Fin m, z i.castSucc
      = (m : R) * (⅟((m : R) + 1) * ∑ j, z j) + a ^ 2 * ∑ i, u' i := by
    have hi : ∀ i : Fin m,
        z i.castSucc = ⅟((m : R) + 1) * ∑ j, z j + a ^ 2 * u' i := by
      intro i
      linear_combination hu' i
    rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hsplit := Fin.sum_univ_castSucc z
  have hlast : z (Fin.last m) - ⅟((m : R) + 1) * ∑ j, z j = a ^ 2 * (-(∑ i, u' i)) := by
    linear_combination -hsplit - hS - (∑ j, z j) * hB
  set u : Fin (m + 1) → R := Fin.snoc u' (-(∑ i, u' i)) with hudef
  have hall : ∀ j, z j - ⅟((m : R) + 1) * ∑ k, z k = a ^ 2 * u j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [hudef]
      simpa using hlast
    | cast i =>
      rw [hudef]
      simp only [Fin.snoc_castSucc]
      exact hu' i
  refine mem_scaledOrder.2 ⟨fun j => ⅟((m : R) + 1) * t + a * u j, ?_, ?_⟩
  · intro j k
    exact ⟨u j - u k, by ring⟩
  · funext j
    show a * (⅟((m : R) + 1) * t + a * u j) = z j
    have hj := hall j
    rw [ht] at hj
    linear_combination -hj

/-- The trace-law defect map on the rescaled dual lattice. -/
noncomputable def scaledTraceCoord (a : R) (m : ℕ) [Invertible ((m : R) + 1)] :
    scaledDual a (m + 1) →ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  (traceCoord a m).comp (scaledDual a (m + 1)).subtype

theorem scaledTraceCoord_surjective :
    Function.Surjective (scaledTraceCoord a m) := by
  intro w
  obtain ⟨z, hz, hzw⟩ := traceCoord_surjective_scaledDual (a := a) w
  exact ⟨⟨z, hz⟩, hzw⟩

theorem scaledTraceCoord_eq_zero_iff (z : scaledDual a (m + 1)) :
    scaledTraceCoord a m z = 0 ↔ (z : Fin (m + 1) → R) ∈ scaledOrder a (m + 1) := by
  constructor
  · intro h
    exact mem_scaledOrder_of_traceCoord z.2 h
  · intro h
    exact traceCoord_scaledOrder h

theorem ker_scaledTraceCoord :
    LinearMap.ker (scaledTraceCoord a m)
      = Submodule.comap (scaledDual a (m + 1)).subtype (scaledOrder a (m + 1)) := by
  ext z
  rw [LinearMap.mem_ker, scaledTraceCoord_eq_zero_iff, Submodule.mem_comap,
    Submodule.subtype_apply]

/-- **Card `(4)`, integral form.**  `(a·A♯)/(a·A) ≅ (R/a²)^{N−1}`. -/
noncomputable def scaledTraceDefectEquiv :
    (scaledDual a (m + 1) ⧸
        Submodule.comap (scaledDual a (m + 1)).subtype (scaledOrder a (m + 1)))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ ker_scaledTraceCoord.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ scaledTraceCoord_surjective)

end TraceDefect

/-! ## The trace-law defect inside the total quotient algebra -/

section DualIntegral

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The dual lattice is the rescaling of its integral model. -/
noncomputable def dualIntegralEquiv (ha : a ≠ 0) :
    scaledDual a (m + 1) ≃ₗ[R] traceDual (K := K) a (m + 1) :=
  (Submodule.equivMapOfInjective _ (dualScaleMap_injective (K := K) ha (m + 1))
      (scaledDual a (m + 1))).trans
    (LinearEquiv.ofEq _ _ (traceDual_eq_map (K := K) ha m).symm)

theorem dualIntegralEquiv_coe (ha : a ≠ 0) (z : scaledDual a (m + 1)) :
    ((dualIntegralEquiv (K := K) ha z : traceDual (K := K) a (m + 1)) : Fin (m + 1) → K)
      = dualScaleMap a (m + 1) (z : Fin (m + 1) → R) := rfl

theorem orderLattice_le_traceDual (ha : a ≠ 0) :
    orderLattice (K := K) a (m + 1) ≤ traceDual (K := K) a (m + 1) := by
  rw [orderLattice_eq_map ha, traceDual_eq_map ha]
  exact Submodule.map_mono (scaledOrder_le_scaledDual a (m + 1))

end DualIntegral

section TraceDefectField

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [Invertible ((m : R) + 1)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The trace-law defect map. -/
noncomputable def traceDefectMap (ha : a ≠ 0) :
    traceDual (K := K) a (m + 1) →ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  (scaledTraceCoord a m).comp (dualIntegralEquiv (K := K) ha).symm.toLinearMap

theorem traceDefectMap_surjective (ha : a ≠ 0) :
    Function.Surjective (traceDefectMap (K := K) (a := a) (m := m) ha) :=
  scaledTraceCoord_surjective.comp (dualIntegralEquiv (K := K) ha).symm.surjective

theorem ker_traceDefectMap (ha : a ≠ 0) :
    LinearMap.ker (traceDefectMap (K := K) (a := a) (m := m) ha)
      = Submodule.comap (traceDual (K := K) a (m + 1)).subtype
          (orderLattice (K := K) a (m + 1)) := by
  ext y
  have hy : dualScaleMap a (m + 1)
      (((dualIntegralEquiv (K := K) ha).symm y : scaledDual a (m + 1)) : Fin (m + 1) → R)
      = (y : Fin (m + 1) → K) := by
    rw [← dualIntegralEquiv_coe ha]
    exact congrArg (fun w : traceDual (K := K) a (m + 1) => (w : Fin (m + 1) → K))
      ((dualIntegralEquiv (K := K) ha).apply_symm_apply y)
  have hzero : traceDefectMap (K := K) ha y = 0 ↔
      (((dualIntegralEquiv (K := K) ha).symm y : scaledDual a (m + 1)) : Fin (m + 1) → R)
        ∈ scaledOrder a (m + 1) :=
    scaledTraceCoord_eq_zero_iff _
  rw [LinearMap.mem_ker, hzero, Submodule.mem_comap, Submodule.subtype_apply,
    orderLattice_eq_map ha, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨_, h, hy⟩
  · rintro ⟨z, hz, hzy⟩
    have hzeq : z
        = (((dualIntegralEquiv (K := K) ha).symm y : scaledDual a (m + 1)) : Fin (m + 1) → R) :=
      dualScaleMap_injective (K := K) ha _ (by rw [hzy, ← hy])
    rwa [hzeq] at hz

/-- **Card `(4)`.**  The trace-law defect `L = A♯/A` of the diagonal congruence order
`A = R·1 + a·R^N` is `(R/a²)^{N−1}`. -/
noncomputable def traceDefectEquiv (ha : a ≠ 0) :
    ((traceDual (K := K) a (m + 1)) ⧸
        Submodule.comap (traceDual (K := K) a (m + 1)).subtype (orderLattice (K := K) a (m + 1)))
      ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (ker_traceDefectMap (K := K) ha).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (traceDefectMap_surjective (K := K) ha))

end TraceDefectField

/-! ## The Dedekind different -/

section Different

variable {R : Type*} [CommRing R] [IsDomain R] {a : R} {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDomain R] [IsFractionRing R K] in
theorem aSmul_mem_congruenceOrder (a : R) {N : ℕ} (v : Fin N → R) :
    (a • v : Fin N → R) ∈ congruenceOrder a N := fun l l' =>
  ⟨v l - v l', by show a * v l - a * v l' = a * (v l - v l'); ring⟩

/-- The Dedekind different `{d : d·A♯ ⊆ A}` inside the total quotient algebra. -/
def dedekindDifferent (a : R) (N : ℕ) : Submodule R (Fin N → K) where
  carrier := {d | ∀ y ∈ traceDual (K := K) a N, d * y ∈ orderLattice (K := K) a N}
  add_mem' := by
    intro d d' hd hd' y hy
    have h : (d + d') * y = d * y + d' * y := by ring
    rw [h]
    exact add_mem (hd y hy) (hd' y hy)
  zero_mem' := by
    intro y _
    have h : (0 : Fin N → K) * y = 0 := by ring
    rw [h]
    exact zero_mem _
  smul_mem' := by
    intro c d hd y hy
    have h : (c • d) * y = c • (d * y) := by
      funext j
      show c • d j * y j = c • (d j * y j)
      rw [Algebra.smul_def, Algebra.smul_def]
      ring
    rw [h]
    exact Submodule.smul_mem _ c (hd y hy)

omit [IsDomain R] [IsFractionRing R K] in
theorem one_mem_traceDual (a : R) (N : ℕ) :
    (1 : Fin N → K) ∈ traceDual (K := K) a N := by
  intro x _
  refine ⟨∑ i, x i, ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    show algebraMap R K (x i) * 1 = algebraMap R K (x i)
    rw [mul_one]

/-- **Card `(26k)`.**  For at least three sheets the Dedekind different is `a²·O`. -/
theorem mem_dedekindDifferent_iff (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    {d : Fin (m + 1) → K} :
    d ∈ dedekindDifferent (K := K) a (m + 1)
      ↔ ∃ w : Fin (m + 1) → R, d = coordIncl R K (m + 1) ((a ^ 2) • w) := by
  classical
  constructor
  · intro hd
    obtain ⟨v, hv, hvd⟩ := hd 1 (one_mem_traceDual a (m + 1))
    have hdv : ∀ j, d j = algebraMap R K (v j) := by
      intro j
      have hj := congrFun hvd j
      rw [coordIncl_apply] at hj
      rw [hj]
      show d j = d j * 1
      rw [mul_one]
    have hdvd : ∀ j, a ^ 2 ∣ v j := by
      have key : ∀ i : Fin m, a ^ 2 ∣ v i.castSucc ∧ a ^ 2 ∣ v (Fin.last m) := by
        intro i
        set z : Fin (m + 1) → R :=
          Pi.single i.castSucc 1 - Pi.single (Fin.last m) 1 with hz
        have hzsum : ∑ j, z j = 0 := by
          rw [hz]
          simp
        have hzmem : dualScaleMap (K := K) a (m + 1) z ∈ traceDual (K := K) a (m + 1) := by
          rw [traceDual_eq_map ha]
          exact ⟨z, mem_scaledDual.2 ⟨0, by rw [hzsum, mul_zero]⟩, rfl⟩
        obtain ⟨u, hu, hud⟩ := hd _ hzmem
        have hcoord : ∀ j, u j * a = v j * z j := by
          intro j
          have hj := congrFun hud j
          rw [coordIncl_apply] at hj
          have hj' : algebraMap R K (u j)
              = algebraMap R K (v j) * (algebraMap R K (z j) / algebraMap R K a) := by
            rw [hj]
            show d j * dualScaleMap (K := K) a (m + 1) z j = _
            rw [dualScaleMap_apply, hdv j]
          refine IsFractionRing.injective R K ?_
          rw [map_mul, map_mul, hj', mul_assoc,
            div_mul_cancel₀ _ (algebraMap_ne_zero_of_ne_zero (K := K) ha)]
        haveI : Nontrivial (Fin m) :=
          ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
        obtain ⟨j₀, hj₀⟩ := exists_ne i
        have hu0 : u j₀.castSucc = 0 := by
          have h := hcoord j₀.castSucc
          have hzj : z j₀.castSucc = 0 := by
            rw [hz]
            show (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) j₀.castSucc
              - (Pi.single (Fin.last m) (1 : R) : Fin (m + 1) → R) j₀.castSucc = 0
            rw [Pi.single_eq_of_ne (fun hc => hj₀ (Fin.castSucc_injective m hc)),
              Pi.single_eq_of_ne (Fin.castSucc_lt_last j₀).ne, sub_zero]
          rw [hzj, mul_zero] at h
          exact (mul_eq_zero.1 h).resolve_right ha
        have hzi : z i.castSucc = 1 := by
          rw [hz]
          show (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) i.castSucc
            - (Pi.single (Fin.last m) (1 : R) : Fin (m + 1) → R) i.castSucc = 1
          rw [Pi.single_eq_same, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, sub_zero]
        have hzl : z (Fin.last m) = -1 := by
          rw [hz]
          show (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) (Fin.last m)
            - (Pi.single (Fin.last m) (1 : R) : Fin (m + 1) → R) (Fin.last m) = -1
          rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne', Pi.single_eq_same, zero_sub]
        obtain ⟨s, hs⟩ := hu i.castSucc j₀.castSucc
        obtain ⟨t, ht⟩ := hu (Fin.last m) j₀.castSucc
        rw [hu0, sub_zero] at hs ht
        constructor
        · refine ⟨s, ?_⟩
          have h := hcoord i.castSucc
          rw [hzi, mul_one] at h
          rw [← h, hs]
          ring
        · refine ⟨-t, ?_⟩
          have h := hcoord (Fin.last m)
          rw [hzl] at h
          have h' : v (Fin.last m) = -(u (Fin.last m) * a) := by linear_combination h
          rw [h', ht]
          ring
      intro j
      induction j using Fin.lastCases with
      | last => exact (key ⟨0, by omega⟩).2
      | cast i => exact (key i).1
    choose w hw using hdvd
    refine ⟨w, ?_⟩
    funext j
    rw [coordIncl_apply, hdv j, hw j]
    rfl
  · rintro ⟨w, rfl⟩ y hy
    obtain ⟨q, hq, hqy⟩ := (traceDual_eq_map (K := K) ha m).le hy
    refine ⟨a • (w * q), aSmul_mem_congruenceOrder a _, ?_⟩
    funext j
    rw [coordIncl_apply]
    show algebraMap R K (a * (w j * q j))
      = algebraMap R K (((a ^ 2) • w) j) * y j
    rw [← hqy, dualScaleMap_apply]
    show _ = algebraMap R K (a ^ 2 * w j) * (algebraMap R K (q j) / algebraMap R K a)
    rw [map_mul, map_mul, map_mul, map_pow]
    field_simp

end Different

end HTGeometry.ConstraintRelativity
